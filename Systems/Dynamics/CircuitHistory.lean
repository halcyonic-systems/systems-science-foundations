/-
  Systems/Dynamics/CircuitHistory.lean
  RESEARCH, reviewed and merged 2026-08-14 — bert-lenses#112, the
  H-instantiation question. See docs/research/112-h-instantiation-plan.md
  for the write-up this file supports; that document is the source of the
  claim boundaries. Review notes: `cbeh_unique` carries the finality
  content; `recordedHistory_eq_orbit_prefix` is definitional by design and
  says so; `circuitTransition` is defined to witness the
  `deterministicClosed` instantiation but is not consumed by the proof
  chain, which works over the abstract `f` directly. NOT a K≅2 headline
  claim (not restated in Challenge.lean); the claim is about the dynamics
  rung at the ABSTRACTED carrier, never about the Rust stepper itself.

  Instantiates `Transition.deterministicClosed` at a simplified but faithful
  abstraction of `bert-compose::Circuit`'s minimal state (a finite node set's
  storage/activity, plus tick/time/ledger totals — the three trace buffers
  excluded per proposal §1.6), and states — with the identity observer
  `outputType := Carrier` — that the recorded history is exactly the
  final-Id-coalgebra's observable behaviour, ported from the hand-written
  (Mathlib-`PFunctor.M`-free) construction in the 2026-07-25 probe
  (`operations/sessions/_archive/July/2026-07-25/references/
  final-coalgebra-probe.lean`, §§1-2 only — the M-type machinery in that
  probe's §3 is NOT ported here; it is not needed for this statement).

  The transition map `f` is kept ABSTRACT. `step_dt`'s actual arithmetic is
  Rust, not reproduced here — this file's content is the coalgebra-shape
  claim, not a reimplementation of the stepper.
-/

import Systems.Dynamics.Transition
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation

namespace Systems
namespace CircuitHistory

/-! ## 1. The carrier — a faithful, minimal abstraction of `Circuit`'s state

    Per proposal §1.2, minus the three circuit-level trace buffers
    (`history`, `ledger_history`, `wire_history`, flagged in §1.6) and minus
    the per-node `total`/`spark` fields (write-only accumulators / a bounded
    UI sparkline — same write-once-never-read-back role as the flagged
    buffers, argued in the companion plan doc; NOT settled by the source
    documents verbatim, flagged there as a judgment call). -/

/-- The per-node fields `step_dt` actually reads AND writes each tick
    (`circuit.rs:477-519`, restricted to `storage`/`activity`). `ι` stands in
    for the circuit's fixed node index set (topology is a *parameter*, not
    state — §1.2). `V` stands in for the numeric type `storage`/`activity`/
    `time`/the ledger totals actually carry (`f32` in Rust) — left abstract
    because none of this file's theorems depend on which ordered field it
    is; `f32` is not itself a Lean/Mathlib type, so a real instantiation
    would pick `ℝ` or `ℚ` at the point this connects to executable code, not
    here. -/
structure Carrier (ι V : Type) where
  /-- Per-node stock level. -/
  storage : ι → V
  /-- Per-node this-tick activity (flow computed by the one-tick map). -/
  activity : ι → V
  /-- Ticks stepped so far. -/
  tick : ℕ
  /-- Accumulated model time (Σ dt), what forced-series lookups index by
      (§1.4). -/
  time : V
  /-- Circuit-level ledger accumulators (`circuit.rs:477-519`). Included
      because they are genuinely mutated by `step_dt`'s write phase
      (`circuit.rs:1383-1384`, the `dissipated` residual at
      `circuit.rs:1331-1352`) — they are accumulators, like the excluded
      per-node `total`, but the target text (proposal §4) names them
      explicitly as part of the carrier ("storage, activity, tick, time,
      ledger totals"), so they are kept and the asymmetry with `total` is
      flagged, not silently resolved. -/
  emitted : V
  sunk : V
  dissipated : V

/-! ## 2. The transition — the closed deterministic instance, `f` abstract

    `f` stands for one call to `step_dt(dt)` at fixed `dt` and fixed circuit
    parameters (topology, node kinds, rates — everything `from_spec` sets
    once, §1.2). This is `deterministicClosed` from `Transition.lean`,
    unchanged; no new machinery, just a choice of `S`. -/

variable {ι V : Type}

/-- One BERT dynamics descriptor: deterministic, discrete, declaring mass as
    an invariant (the ledger's own `final_balance ≈ 0` intent, §1.7 — a
    DECLARATION, not a derived guarantee; the tRNA pathology in §1.7 shows
    the declared invariant can fail to hold for a badly-classified model,
    which is exactly what `invariants` being declared-not-derived means,
    `Record.lean:79-83`). -/
def circuitDynamics (ι V : Type) : Dynamics (Carrier ι V) :=
  Dynamics.conservationExample (Carrier ι V)

/-- A closed-deterministic transition for a fixed one-tick map `f`. -/
def circuitTransition (f : Carrier ι V → Carrier ι V) :
    Transition (circuitDynamics ι V) :=
  Transition.deterministicClosed f

/-! ## 3. The recorded run — a finite prefix of the orbit -/

/-- The internal-trajectory reading of a recorded run (issue #97's
    ratified reading, "process = sequence of states"): the state after each
    of the first `n` ticks, starting from `x0`, INCLUDING `x0` itself at
    index 0. In the engine that is `RecordedRun.start` followed by the `n`
    rows of `RecordedRun.history`: `history` holds one row per tick and no
    starting row, and `start` carries `x0` (facets `run.rs`, `record`;
    `start` since facets walk row 47, 2026-11-04). An earlier version of
    this docstring said `history` itself held the starting row; it never
    did (facets walk row 41). -/
def recordedHistory (f : Carrier ι V → Carrier ι V) (x0 : Carrier ι V) (n : ℕ) :
    List (Carrier ι V) :=
  (List.range (n + 1)).map (fun i => f^[i] x0)

/-- The orbit of `f` from `x0` — Bunge's "a process is a sequence of
    states," read internally (ported verbatim from the probe, §2). -/
def orbit (f : Carrier ι V → Carrier ι V) (x0 : Carrier ι V) : ℕ → Carrier ι V :=
  fun n => f^[n] x0

/-- `recordedHistory` is definitionally the finite prefix of `orbit` — the
    engineering-naming bridge between `RecordedRun.history` (a `Vec`, in
    Rust) and the coalgebraic `orbit` (a stream, in Lean). This direction of
    the claim needs no coalgebra machinery; it is true by how `history` is
    built (append one `orbit`-step per tick). -/
theorem recordedHistory_eq_orbit_prefix (f : Carrier ι V → Carrier ι V)
    (x0 : Carrier ι V) (n : ℕ) :
    recordedHistory f x0 n = (List.range (n + 1)).map (orbit f x0) := rfl

/-! ## 4. The final-coalgebra reading — ported from the probe, §§1-2

    Hand-built (no `PFunctor.M`, no `Classical.choice` dependency — see the
    probe's own axiom audit, §4 of that file): for `F X = (B × X)^A` the
    final coalgebra is the set of causal functions `A⁺ → B`. Specialised to
    `A := Unit` (closed, no live input port — §1.5's finding) and
    `B := Carrier ι V` (the identity observer, `outputType := Carrier` — the
    non-degeneracy fix from the 2026-07-25 comment), the final-coalgebra
    carrier collapses to `ℕ → Carrier ι V`, an output stream — exactly the
    behaviour reading `orbit` already gives. -/

/-- A word of `Unit`-inputs plus one more, mapping to a `Carrier ι V` output
    — the closed, `Carrier`-observed final-coalgebra carrier before the
    stream-collapse identification. -/
def Causal (ι V : Type) : Type := List Unit → Unit → Carrier ι V

/-- The final coalgebra's own structure map: next output, plus the
    derivative (ported verbatim from the probe). -/
def Causal.step (f : Causal ι V) : Unit → Carrier ι V × Causal ι V :=
  fun a => (f [] a, fun w a' => f (a :: w) a')

/-- The behaviour map out of an arbitrary closed-deterministic coalgebra
    (ported verbatim from the probe, generalized only in the output type). -/
def cbeh (step : Unit → Carrier ι V → Carrier ι V × Carrier ι V) :
    Carrier ι V → Causal ι V :=
  fun s w a =>
    match w with
    | []      => (step a s).1
    | x :: xs => cbeh step (step x s).2 xs a

/-- `cbeh` is a coalgebra morphism (ported verbatim). -/
theorem cbeh_morphism
    (step : Unit → Carrier ι V → Carrier ι V × Carrier ι V) (s : Carrier ι V) :
    Causal.step (cbeh step s)
      = fun a => ((step a s).1, cbeh step (step a s).2) := rfl

/-- **Finality**, ported verbatim: any coalgebra morphism into `Causal ι V`
    equals `cbeh`. -/
theorem cbeh_unique
    (step : Unit → Carrier ι V → Carrier ι V × Carrier ι V)
    (g : Carrier ι V → Causal ι V)
    (hyp : ∀ s, Causal.step (g s)
      = fun a => ((step a s).1, g (step a s).2)) :
    g = cbeh step := by
  funext s w
  induction w generalizing s with
  | nil =>
      funext a
      have := congrFun (hyp s) a
      exact congrArg Prod.fst this
  | cons x xs ih =>
      funext a
      have h := congrFun (hyp s) x
      have h2 : (fun w a' => g s (x :: w) a') = g (step x s).2 :=
        congrArg Prod.snd h
      calc g s (x :: xs) a = (fun w a' => g s (x :: w) a') xs a := rfl
        _ = g (step x s).2 xs a := by rw [h2]
        _ = cbeh step (step x s).2 xs a := by rw [ih]
        _ = cbeh step s (x :: xs) a := rfl

theorem replicate_length_unit : ∀ w : List Unit, List.replicate w.length () = w
  | []       => rfl
  | () :: xs => congrArg (fun l => () :: l) (replicate_length_unit xs)

/-- With a `Carrier`-valued output port and no live input port, `H` (the
    final coalgebra, `Causal ι V`) is exactly the output STREAM `ℕ →
    Carrier ι V` (ported verbatim from the probe). -/
def causalOutputOnly : Causal ι V ≃ (ℕ → Carrier ι V) where
  toFun f := fun n => f (List.replicate n ()) ()
  invFun g := fun w _ => g w.length
  left_inv f := by
    funext w a
    cases a
    show f (List.replicate w.length ()) () = f w ()
    exact congrArg (fun l => f l ()) (replicate_length_unit w)
  right_inv g := by
    funext n
    exact congrArg g (List.length_replicate ..)

/-- **The target theorem.** Declaring the state itself as the observable
    (`outputType := Carrier ι V`, `inputType := Unit` — the identity-
    observer fix the 2026-07-25 comment names as what avoids the closed-
    deterministic degeneracy), the observable behaviour of `x0` under the
    final Id-Mealy-coalgebra reading — `cbeh`, transported along
    `causalOutputOnly` — IS `orbit f x0`. Nothing about the descriptor
    changes but the choice of port; this is `Transition.deterministicClosed`
    read through the finality argument above, not a new construction. -/
theorem history_is_final_coalgebra_behaviour (f : Carrier ι V → Carrier ι V)
    (x0 : Carrier ι V) :
    causalOutputOnly (cbeh (fun (_ : Unit) (t : Carrier ι V) => (t, f t)) x0)
      = orbit f x0 := by
  funext n
  show cbeh (fun (_ : Unit) (t : Carrier ι V) => (t, f t)) x0
        (List.replicate n ()) () = f^[n] x0
  induction n generalizing x0 with
  | zero => rfl
  | succ m ih =>
      show cbeh (fun (_ : Unit) (t : Carrier ι V) => (t, f t)) (f x0)
            (List.replicate m ()) () = f^[m + 1] x0
      rw [ih, Function.iterate_succ_apply]

/-- Chaining the two theorems: `RecordedRun.history`, for the abstracted
    `Circuit` carrier and one-tick map `f`, is a finite prefix of the
    Carrier-observed final-Id-coalgebra's behaviour map at `x0`. This is the
    top-level claim this file was built to state. -/
theorem recordedHistory_is_coalgebra_prefix (f : Carrier ι V → Carrier ι V)
    (x0 : Carrier ι V) (n : ℕ) :
    recordedHistory f x0 n
      = (List.range (n + 1)).map
          (causalOutputOnly
            (cbeh (fun (_ : Unit) (t : Carrier ι V) => (t, f t)) x0)) := by
  rw [recordedHistory_eq_orbit_prefix, history_is_final_coalgebra_behaviour]

/-! ## 5. Stoichiometric conservation, for any rates (facets #573)

    A work process with a mass-action law moves its stocks by a fixed
    pattern times a rate: one reaction `j` changes stock `i` by
    `N i j * r j`, where `N` is the stoichiometric matrix (species by
    reactions) and `r` the tick's rates. Facets #573 needs this: if a row
    vector `ℓ` has `ℓ ᵥ* N = 0`, then `ℓ ⬝ᵥ x` is conserved by every step,
    whatever the rates are, so a rate law (mass action, or any other) can
    never break a conservation that the pattern already has (SIR's
    `S + I + R`, predator-prey's matter if the prey are booked).

    The rates may depend on the tick and on the state (`rates n x`), which
    covers mass action `k * ∏ x_i` read from the opening state, and covers
    a non-negativity cap **only if the cap scales a whole reaction's rate**
    `r j`. A cap that clips one stock's change and not its partners' is a
    step outside this form, and the lemma says nothing about it.

    What this is not: a statement about the Rust stepper. `R` is any
    commutative ring (read `ℚ` or `ℝ`); the engine computes in `f64` and
    rounds, which this file does not model. The two theorems use Mathlib's
    finite sums, so their audit lists `Classical.choice` (with `propext` and
    `Quot.sound`); the sections above keep their own, smaller audits. -/

section Stoichiometry

open Matrix

variable {σ ρ R : Type} [Fintype σ] [Fintype ρ] [CommRing R]

/-- One step of a stoichiometric system: the state moves by `N *ᵥ r`. -/
def stoichStep (N : Matrix σ ρ R) (x : σ → R) (r : ρ → R) : σ → R :=
  x + N *ᵥ r

/-- A run: at tick `n` the rates are `rates n x`, read from the opening
    state `x` of that tick. -/
def stoichRun (N : Matrix σ ρ R) (rates : ℕ → (σ → R) → (ρ → R))
    (x0 : σ → R) : ℕ → σ → R
  | 0 => x0
  | n + 1 => stoichStep N (stoichRun N rates x0 n) (rates n (stoichRun N rates x0 n))

/-- A left null vector of `N` gives a quantity one step conserves, for any
    rates. -/
theorem stoichStep_conserves (N : Matrix σ ρ R) (ℓ : σ → R) (h : ℓ ᵥ* N = 0)
    (x : σ → R) (r : ρ → R) :
    ℓ ⬝ᵥ stoichStep N x r = ℓ ⬝ᵥ x := by
  rw [stoichStep, dotProduct_add, Matrix.dotProduct_mulVec, h, zero_dotProduct,
    add_zero]

/-- And so every tick of a run conserves it, whatever the rate law. -/
theorem stoichRun_conserves (N : Matrix σ ρ R) (ℓ : σ → R) (h : ℓ ᵥ* N = 0)
    (rates : ℕ → (σ → R) → (ρ → R)) (x0 : σ → R) (n : ℕ) :
    ℓ ⬝ᵥ stoichRun N rates x0 n = ℓ ⬝ᵥ x0 := by
  induction n with
  | zero => rfl
  | succ m ih => rw [stoichRun, stoichStep_conserves N ℓ h, ih]

/-- The SIR pattern, checked: infection moves one from S to I, recovery one
    from I to R, so `(1, 1, 1)` is a left null vector and the town's total
    is conserved by any infection and recovery rates. -/
example : (fun _ => (1 : ℚ)) ᵥ* (!![-1, 0; 1, -1; 0, 1] : Matrix (Fin 3) (Fin 2) ℚ)
    = 0 := by
  ext j; fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three]

end Stoichiometry

section Audit
#print axioms recordedHistory_eq_orbit_prefix
#print axioms cbeh_morphism
#print axioms cbeh_unique
#print axioms replicate_length_unit
#print axioms causalOutputOnly
#print axioms history_is_final_coalgebra_behaviour
#print axioms recordedHistory_is_coalgebra_prefix
#print axioms stoichStep_conserves
#print axioms stoichRun_conserves
end Audit

end CircuitHistory
end Systems
