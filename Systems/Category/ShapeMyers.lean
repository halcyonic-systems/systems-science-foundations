/-
Copyright (c) 2026 Shingai Thornton. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Shingai Thornton
-/
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Shape Category for Myers's Deterministic Systems (Lenses)

The *shape category* `I_Myers` encodes the dependency structure of Myers's
deterministic system definition S = ⟨State, Out, In, expose, update⟩
(Categorical Systems Theory, Def 1.2.1.2, 2023).

## Construction

3 objects (`state`, `output`, `input`) and 2 generating arrows (`expose`, `update`).
The arrows follow the dependency convention: the update function depends on both
state and input, so arrows go from state toward what it produces/consumes.

## Arrow Direction Convention

Same as Bunge/Mobus: arrows point from the *dependent* to what it *depends on*.
- `expose : state → output` — the expose function reads state to produce output
- `update : state → input` — the update function consumes input to modify state

Note: `update` semantically has type `State × In → State`, so it depends on BOTH
state and input. We model the input-dependency as the generating arrow. The
self-dependency (State → State) is implicit in the identity morphism at `state`.

## Relationship to Lenses

A Myers deterministic system IS a lens `(State, State) ⇆ (In, Out)` where:
- passforward = `expose : State → Out`
- passback = `update : State × In → State`

The shape category captures the *positional* structure without the product/lens machinery.
The comparison functor `I_Myers → I_Mobus` (or reverse) establishes that BERT's system
coupling is an instance of lens composition.
-/

/-- The three positions in Myers's deterministic system definition.

- `state`: State_S — the set of internal states
- `output`: Out_S — values of exposed variables (what the system reveals)
- `input`: In_S — parameter values (what the system consumes from its environment)
-/
inductive MyersPosition
  | state
  | output
  | input
  deriving DecidableEq, Inhabited

/-- Generating morphisms for the Myers shape quiver.

- `expose`: state depends on output (expose reads state to produce output)
- `update`: state depends on input (update consumes input to advance state)

These correspond to the two functions in the 5-tuple:
- `expose_S : State_S → Out_S`
- `update_S : State_S × In_S → State_S`
-/
inductive MyersArrow : MyersPosition → MyersPosition → Type
  | expose : MyersArrow .state .output
  | update : MyersArrow .state .input

instance : Quiver MyersPosition where
  Hom := MyersArrow

open CategoryTheory in
/-- The shape category for Myers's deterministic systems: the free category on the lens quiver.

This is the simplest shape category in the landscape: 3 objects, 2 arrows, no composable
chains (state is the only source, output and input are sinks). Every non-identity
morphism is a generating arrow — no composite paths exist.

The minimality of this shape is precisely Myers's design choice: he encodes ALL
compositional complexity in the lens/arena machinery rather than in the system definition
itself. The comparison functor `I_Mobus → I_Myers` will show what Mobus carries
structurally that Myers delegates to the categorical framework. -/
abbrev MyersShape := Paths MyersPosition
