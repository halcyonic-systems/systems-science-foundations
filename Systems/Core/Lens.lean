/-
  Systems/Core/Lens.lean
  Bidirectional transformations: the mathematical primitive of cybernetic feedback

  Three independent research programs converge on lenses as the building
  block of feedback systems:
  - Capucci et al. 2022: parametrised optics in categorical cybernetics
  - Joyal-Street-Verity 1996: traced monoidal categories
  - Spivak-Niu 2024: polynomial functors and coalgebras

  A lens (S, A, B) captures a bidirectional channel:
    get : S → A    (forward: observe/extract)
    put : S → B → S (backward: update/correct)

  Our Homeostat IS a lens equipped with a reference value. Defining this
  explicitly connects the Mobus/Bunge/Klir grounding to the entire modern
  categorical cybernetics literature. Myers's CST (2023) makes this precise:
  a deterministic system is a lens (State,State) ⇆ (In,Out). ShapeMyers.lean
  encodes the positional structure; this file provides the algebraic structure.

  In Set (our Lean types), Lens ≅ Optic_× (Capucci Remark 9). No need for
  the full optic machinery — lenses suffice for cartesian monoidal categories.
-/

import Systems.Core.Dynamics

namespace Systems

/-! ## Lens: the bidirectional channel primitive -/

/-- A lens: the basic bidirectional transformation.

    `S` is the source (whole state), `A` is the forward view (observation),
    `B` is the backward update (correction signal). The asymmetric form
    (A ≠ B) supports cases where the observation type differs from the
    correction type. For homeostats, A = B = O (observation space).

    In polynomial functor language: a lens S A B is a morphism of
    polynomial functors Sy^S → Ay^B. Our shape categories encode
    polynomial interface patterns; this structure provides the algebra. -/
@[ext]
structure Lens (S A B : Type*) where
  get : S → A
  put : S → B → S

/-- Symmetric lens: forward and backward share a type. -/
abbrev SymLens (S A : Type*) := Lens S A A

/-! ## Lens composition

  Lenses compose by threading get forward and put backward through
  the intermediate state. This gives governance composition for free:
  composing two homeostats' lenses produces a well-defined composed
  bidirectional channel without bespoke construction. -/

/-- Compose two symmetric lenses through an intermediate state.

    Given l₁ : SymLens S A (outer) and l₂ : SymLens A C (inner):
    - get: observe C from S by observing A first, then C
    - put: to update S with a C, first get the intermediate A from S,
      update A with C via l₂, then update S with the new A via l₁

    Composition requires symmetric lenses (forward and backward types
    match) because l₂.put returns A, which must be the type l₁.put
    accepts. Asymmetric lens composition requires profunctor optics —
    future work if needed for non-governance applications.

    This is the standard lens composition from Capucci et al. (2022)
    and Spivak-Niu (2024). It gives governance composition structurally. -/
def Lens.compose {S A C : Type*}
    (l₁ : SymLens S A) (l₂ : SymLens A C) : SymLens S C where
  get := l₂.get ∘ l₁.get
  put := fun s c => l₁.put s (l₂.put (l₁.get s) c)

/-- The identity lens: observe the whole state, replace it entirely. -/
def Lens.id (S : Type*) : SymLens S S where
  get := _root_.id
  put := fun _ s => s

/-! ## Lens laws (associativity and identity)

  Symmetric lenses form a category: composition is associative with
  identity. This is the algebraic foundation for hierarchical governance
  at arbitrary depth without bespoke construction at each level. -/

/- PROOF TARGET: Lens composition is associative.

   MATHEMATICAL INTENT:
   Three-fold lens composition yields the same result regardless of
   bracketing. Together with identity, this makes SymLens a category.

   AVAILABLE TOOLS:
   - `Lens.compose` definition (function composition + put threading)
   - `@[ext]` on Lens (extensionality: two lenses equal iff get/put agree)

   STRATEGY HINT:
   ext decomposes to get and put components; both should be rfl
   (definitional equality via function composition associativity). -/
theorem Lens.compose_assoc {S A C E : Type*}
    (l₁ : SymLens S A) (l₂ : SymLens A C) (l₃ : SymLens C E) :
    (l₁.compose l₂).compose l₃ = l₁.compose (l₂.compose l₃) := by
  ext <;> rfl

theorem Lens.id_compose {S A : Type*} (l : SymLens S A) :
    (Lens.id S).compose l = l := by
  ext <;> rfl

theorem Lens.compose_id {S A : Type*} (l : SymLens S A) :
    l.compose (Lens.id A) = l := by
  ext <;> simp [Lens.compose, Lens.id]

/-! ## Well-behavedness laws

  The three lens laws (GetPut, PutGet, PutPut) characterize
  "well-behaved" lenses — those where get and put are coherent.
  These are predicates on symmetric lenses, not baked into the
  structure, following the project convention of separating data
  from constraints (cf. RecursiveSystem vs WellFormed). -/

def Lens.GetPut {S A : Type*} (l : SymLens S A) : Prop :=
  ∀ s, l.put s (l.get s) = s

def Lens.PutGet {S A : Type*} (l : SymLens S A) : Prop :=
  ∀ s a, l.get (l.put s a) = a

def Lens.PutPut {S A : Type*} (l : SymLens S A) : Prop :=
  ∀ s a₁ a₂, l.put (l.put s a₁) a₂ = l.put s a₂

/-! ## Conant-Ashby Skeleton

  Conant & Ashby (1970): "Every good regulator of a system must be
  a model of that system." The structural skeleton: governance requires
  a homomorphism from the regulator's state space to the system's state
  space, preserving observational structure.

  The commuting diagram:

      R ——model——→ S
      |              |
   regView        observe
      |              |
      ↓              ↓
      O ============ O

  This IS the walking arrow. The morphism model : R → S makes the
  diagram commute: observe ∘ model = regView. K ≅ **2** says a system
  IS a morphism (relations depend on things). Conant-Ashby says a good
  regulator IS a morphism (regulator models system). Both are instances
  of the walking arrow **2**. The irreducible categorical content of
  "being a system" and "governing a system" is the same structure.

  The full Conant-Ashby theorem is information-theoretic (entropy on
  stochastic channels proves the simplest optimal regulator is
  deterministic → the optimal regulator IS a model). The structural
  claim — that a homomorphism must exist — is the combinatorial
  skeleton. The entropy proof requires measure theory not in scope. -/
structure ConantAshbySkeleton (R S O : Type*) where
  /-- The regulator's homomorphic model of the system -/
  model : R → S
  /-- The system's observation map (sensor) -/
  observe : S → O
  /-- The regulator's own view of its state -/
  regView : R → O
  /-- The model is compatible with observation: the diagram commutes. -/
  model_compatible : observe ∘ model = regView

end Systems
