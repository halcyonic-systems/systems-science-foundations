/-
  Systems/Dynamics/Transition.lean
  The typed transition — #112 Half A, step 1.

  Gives a `Dynamics` descriptor its transition function, TYPED BY THE KIND. This is
  the coalgebra structure map `T : S → F(S)`, Mealy-wrapped over the descriptor's
  ports: `F(X) = kindCodomain kind X`, and the transition reads an `inputType`,
  emits an `outputType`. THE TYPE IS THE CHECK — a value of `Transition d` is, by
  construction, a transition of `d`'s declared kind; "the transition matches the
  kind" is enforced by the elaborator, not a separate runtime gate.

  OWN THE DEFINITION (frontier-council, 2026-07-23). `kindCodomain` is BERT's own
  definition; the correspondence to Rutten's coalgebra functors and Spivak's Poly
  is a COMMENT, never an import — so no external, moving theory can invalidate the
  kernel.

  HOMOGENEOUS / PER-KIND ONLY. Composing transitions of DIFFERENT kinds in one
  system is heterogeneous open composition — the open research frontier (Half B),
  deliberately absent here.

  AXIOM-FREE and CONSERVATIVE. Markov is Nat-weighted finite successors (the
  bert-lenses#67 "real counts" form), so no Mathlib distribution type is pulled in;
  the file adds to `Dynamics` and touches no existing theorem.
-/

import Systems.Dynamics.Record

namespace Systems

/-- The endofunctor a kind names, as BERT's own definition:
    - `deterministic` ↝ `Id`  (— Rutten `F X = X`)
    - `markov`        ↝ Nat-weighted finite successors (— Rutten `F X = Dist X`,
      here the finite, weight-counted form of bert-lenses#67; no Mathlib `PMF`)
    - `nondeterministic` ↝ finite successor list (— Rutten `F X = 𝒫 X`, the
      life-cycle `ΔS ∈ F(S)` in its finite form).

    The finiteness is not a convenience, and Rutten's `Dist`/`𝒫` are the
    citation, never the type. Wrapped over the descriptor's ports these are
    polynomial (container) functors, so a final coalgebra always exists and `H`
    is well defined; **unrestricted `𝒫` has no final coalgebra in `Set`**
    (Adámek–Milius–Velebil, MSCS 15 (2005), Ex. 3.14), so a kernel typed on it
    could not carry `H`-as-behaviour at all. Do not "generalise" these to
    `Dist`/`𝒫`. Settled 2026-07-25, with a compiled `#print axioms` probe:
    vault `operations/sessions/2026-07-25/references/final-coalgebra-existence.md`. -/
def kindCodomain (k : DynamicsKind) (X : Type) : Type :=
  match k with
  | .deterministic    => X
  | .markov           => List (X × Nat)
  | .nondeterministic => List X

/-- The typed transition over a descriptor: the coalgebra structure map, Mealy-
    shaped over the ports. For a closed descriptor (`inputType = outputType =
    Unit`) the field type reduces to `Unit × S → kindCodomain kind (Unit × S)`,
    i.e. essentially `S → F(S)`. -/
structure Transition {S : Type} (d : Dynamics S) where
  step : d.inputType × S → kindCodomain d.kind (d.outputType × S)

namespace Transition

/-- A deterministic closed transition is exactly a self-map `S → S` — the shape of
    a conservation-flow step (Euler-stepped), now TYPED as the deterministic
    coalgebra. -/
def deterministicClosed {S : Type} (f : S → S) :
    Transition (Dynamics.conservationExample S) where
  step := fun (_, s) => ((), f s)

/-- A Markov closed transition maps a state to its Nat-weighted successors — the
    absorbing chain of bert-lenses#67, TYPED as the markov coalgebra. -/
def markovClosed {S : Type} (succ : S → List (S × Nat)) :
    Transition (Dynamics.billMarkovDescriptor S) where
  step := fun (_, s) => (succ s).map (fun p => (((), p.1), p.2))

/-- The type is the check, made concrete: a closed deterministic transition is
    definitionally the self-map it was built from. The coalgebra framing adds no
    obligation to a single flow — it NAMES it (the survey's "vacuous in isolation"
    caveat, precise: the content is cross-kind, not per-kind). -/
example {S : Type} (f : S → S) (s : S) :
    (deterministicClosed f).step ((), s) = ((), f s) := rfl

/-- A concrete closed Markov step computes its Nat-weighted successors with the
    (closed) ports wrapped on — the #67 absorbing-chain data, Mealy-shaped. -/
example {S : Type} (a b : S) :
    (markovClosed (fun _ => [(a, 1), (b, 2)])).step ((), a)
      = [(((), a), 1), (((), b), 2)] := rfl

end Transition
end Systems
