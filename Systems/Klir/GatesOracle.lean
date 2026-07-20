/-
  Systems/Klir/GatesOracle.lean
  Rung 1.5 of the lens-entry binding (bert-lenses#24): the `lake exe` oracle.

  Rung 1 (GatesTruthTable.lean) enumerates every small (T, R) kernel for n ≤ 2
  into a committed JSON fixture, and a Rust CI test checks the `bert-core` gates
  against those rows. That check is bounded — it can only disagree on a row
  someone thought to enumerate. This oracle removes the bound: it evaluates the
  SAME Lean gate declarations (`hasBondB` / `irreflexiveB`, instantiated at ℕ)
  on an arbitrary (T, R) model handed to it on stdin, so a Rust property test can
  generate models past n = 2 and cross-check each one against Lean at test time.

  Zero FFI: the Rust side shells out to this executable (`lake exe gates-oracle`
  or the prebuilt binary) and speaks JSON over a pipe. Lean's C ABI is officially
  unstable; a subprocess sidesteps it entirely (bert-lenses#24, 2026-07-11
  binding research).

  ── JSON CONTRACT ──────────────────────────────────────────────────────────
  STDIN accepts either one model object or a JSON array of model objects:

    { "n": 3, "things": [0,1,2], "dep": [[0,1],[1,2]] }

  Only `dep` is load-bearing — the gates are pairwise properties of the
  dependency, read as a list of [i, j] index pairs. `n` and `things` are echoed
  back for provenance and are optional (`n` defaults to 0 if absent).

  STDOUT mirrors the shape of a GatesTruthTable fixture row (minus the enumerator
  bookkeeping): the two gate verdicts plus the four mode-entry rights they
  license, via the shared `modesOf`. A single object in ⇒ a single object out; an
  array in ⇒ an array out, index-aligned.

    { "n": 3,
      "dep": [[0,1],[1,2]],
      "gates": { "has_bond": true, "irreflexive": true },
      "modes": { "core": true, "structural": true,
                 "operational": true, "full": true } }

  Malformed input ⇒ a message on stderr and a nonzero exit; stdout stays empty.

  Run:  lake exe gates-oracle < model.json
-/

import Lean.Data.Json
import Systems.Klir.Gates

open Lean (Json ToJson toJson)
open Systems.GatesTruthTable

namespace Systems.GatesOracle

/-- A parsed model: the relata count (echoed) and the dependency as index pairs.
    The gates read only `dep`; `n` is provenance. -/
structure Model where
  n : Nat
  dep : List (Nat × Nat)

/-- Parse one `[i, j]` dependency pair. -/
def parsePair (j : Json) : Except String (Nat × Nat) := do
  let arr ← j.getArr?
  match arr[0]?, arr[1]? with
  | some a, some b => return (← a.getNat?, ← b.getNat?)
  | _, _ => throw s!"dependency entry must be a pair [i, j], got {j.compress}"

/-- Parse one model object. `dep` is required; `n` defaults to 0 when absent. -/
def parseModel (j : Json) : Except String Model := do
  let n : Nat := ((j.getObjVal? "n").bind Json.getNat?).toOption.getD 0
  let depJson ← j.getObjVal? "dep"
  let depArr ← depJson.getArr?
  let dep ← depArr.toList.mapM parsePair
  return { n := n, dep := dep }

/-- The verdict for one model, built from the SAME gate declarations the fixture
    enumerator uses (`hasBondB` / `irreflexiveB` at ℕ) and the SAME mode mapping
    (`modesOf`). This is the whole point of Rung 1.5: no re-implementation to
    drift from. -/
def verdict (m : Model) : Json :=
  let hb := hasBondB (α := Nat) m.dep
  let irr := irreflexiveB (α := Nat) m.dep
  let modes := modesOf hb irr
  Json.mkObj [
    ("n", toJson m.n),
    ("dep", toJson (m.dep.map fun p => #[p.1, p.2])),
    ("gates", Json.mkObj [("has_bond", toJson hb), ("irreflexive", toJson irr)]),
    ("modes", Json.mkObj [
      ("core", toJson modes.core),
      ("structural", toJson modes.structural),
      ("operational", toJson modes.operational),
      ("full", toJson modes.full)])
  ]

/-- Parse stdin, evaluate, and render the response string. An array in yields an
    array out (index-aligned); anything else is treated as a single model. -/
def run (input : String) : Except String String := do
  let j ← Json.parse input
  match j with
  | .arr models =>
    let verdicts ← models.toList.mapM fun jm => verdict <$> parseModel jm
    return (Json.arr verdicts.toArray).compress
  | _ =>
    let m ← parseModel j
    return (verdict m).compress

end Systems.GatesOracle

/-- Entry point: read the whole of stdin, print the verdict(s) to stdout, or
    report a parse error on stderr and exit nonzero. -/
def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  match Systems.GatesOracle.run input with
  | .ok out => IO.println out
  | .error e =>
    (← IO.getStderr).putStrLn s!"gates-oracle: {e}"
    IO.Process.exit 1
