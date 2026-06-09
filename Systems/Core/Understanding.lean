/-
  Systems/Core/Understanding.lean
  Principle 11: Understandability — "Systems can be understood." (Science.)

  Mobus labels #11 a COROLLARY of Internal Models (#9). This file argues, formally,
  that the corollary framing is backwards, and that #11 adds genuine content #9 lacks.

  THE CLAIM #9 ALONE CANNOT MAKE.
  Having a model of S (#9) is not the same as UNDERSTANDING S. The identity model —
  R = S, model = id, dynamics copied across — is a perfectly good InternalModel
  (it simulates S one step at a time, vacuously). But it understands nothing: it
  has duplicated S, not compressed it. Understanding requires a model STRICTLY
  SIMPLER than the thing modelled. That is a claim about the compressibility of
  nature, and #9 never makes it.

  THE FORMALIZATION (compression / Klir's epistemological coarse-graining; Rosen's
  encoding e : N → F from the modelling relation).
  An `Understanding` of S is an abstraction `abstract : S → M` onto a model space M,
  whose dynamics `modelDyn` commute with S's dynamics one step at a time, and which
  is:
  - SURJECTIVE — M is a genuine quotient, no junk states; every model state means
    something in S;
  - NON-INJECTIVE (`compresses`) — distinct system states collapse to one model
    state. This is the strict-simplification requirement; and
  - NON-DEGENERATE (`nontrivial : Nontrivial M`) — the model retains at least one
    distinction.

  WHY `nontrivial` IS REQUIRED (a finding in itself). Without it the definition is
  degenerate: the TOTAL COLLAPSE `abstract : S → Unit` is surjective and lossy and its
  one-step square commutes vacuously, so *every* system with ≥ 2 states would be
  "understood" by throwing all its structure away. But a model that distinguishes
  nothing predicts nothing — it is not an understanding. Requiring `Nontrivial M`
  (the model keeps ≥ 2 distinguishable states) excludes the useless total collapse and
  forces a PROPER coarse-graining: strictly between the identity (no compression) and
  the point (no information).

  DUALITY WITH #9. An InternalModel decodes: `model : R → S` (representation → reality).
  An Understanding encodes: `abstract : S → M` (reality → representation). They are
  dual arrows. Conflating a structure with its dual is part of why "corollary" misleads.

  WHAT IS PROVED.
  - `Understanding.tracks` / `predict_correct`: a correct one-step abstraction predicts
    the system at EVERY horizon — running the simple model forward = the true future,
    coarse-grained. (The #11 analogue of `InternalModel.tracks`.)
  - `Understanding.equilibrium_image`: understanding preserves rest states.
  - `Understanding.card_lt` / `hartley_lt`: on finite carriers the model is STRICTLY
    smaller — fewer states, strictly lower Hartley nonspecificity (#7). The quantitative
    face of "simpler than the modelled."
  - `InternalModel.refl`: every system trivially models itself — #9 is always free.
  - `no_trivial_understanding`: the identity map is not an understanding (even a perfect
    full-resolution model is not understanding).
  - `modeling_does_not_imply_understanding`: a one-state system has a model but admits
    NO understanding (nothing to compress) — the minimal #9 ⇏ #11 witness.
  - `cyclic3_no_understanding` / `cyclic3_modeling_not_understanding`: the STRONGER
    witness — a three-state system with rich dynamics (the 3-cycle `x ↦ x+1`) that has
    a model yet cannot be understood, because 3 is prime: its only dynamics-respecting
    collapse is the total one, which `nontrivial` excludes. Understanding fails here not
    for lack of room to compress, but because the DYNAMICS forbid any informative
    quotient.

  THE FINDING. #11 ⟹ (a model exists) but (a model exists) ⇏ #11. The compression
  requirement is independent content. Understandability is the *compression refinement*
  of Internal Models, not a corollary of it — if anything #9 is the corollary of #11
  (to understand is, a fortiori, to model). This is the "hidden epistemological axiom"
  the roadmap flagged: models must be simpler than the modelled.

  Bridge to Complexity (#5): the fibres of `abstract` (preimages of model states) are
  equivalence classes on S — the same lumping `SameKind` performs on components in
  Complexity.lean. Understanding is structural complexity, reduced.

  Deferred (research-level): the Rosen commuting-square with an explicit decode section;
  the categorical "faithful functor from a simpler shape category" version.
-/

import Systems.Core.InternalModel
import Systems.Core.Information

namespace Systems

/-! ## Understanding as proper (strict, non-degenerate) compression -/

/-- An `Understanding` of a system with dynamics `systemDyn : S → S`: a coarse-graining
    `abstract : S → M` onto a model space `M`, with model dynamics `modelDyn : M → M`
    that commute with the system one step at a time (`abstracts`), where the
    coarse-graining is **onto** (`surjective`), **lossy** (`compresses`: not injective),
    and the model is **non-degenerate** (`nontrivial`: at least two distinguishable
    model states, ruling out the useless total collapse to a point).

    The `compresses` field is the content #9 lacks; the `nontrivial` field keeps the
    compression honest — a proper quotient, not the everything-to-one-point map. -/
structure Understanding (S M : Type*) where
  /-- The coarse-graining of system states to model states (Rosen's encoding). -/
  abstract : S → M
  /-- The actual dynamics of the system. -/
  systemDyn : S → S
  /-- The induced dynamics on the model space. -/
  modelDyn : M → M
  /-- One-step commuting square: abstracting then stepping the model equals
      stepping the system then abstracting. -/
  abstracts : ∀ s, abstract (systemDyn s) = modelDyn (abstract s)
  /-- The model space is a genuine quotient: every model state is realised. -/
  surjective : Function.Surjective abstract
  /-- Strict simplification: distinct system states share a model state. -/
  compresses : ¬ Function.Injective abstract
  /-- Non-degenerate: the model retains at least one distinction (excludes the
      total collapse to a single point, which would "understand" everything). -/
  nontrivial : Nontrivial M

/-! ## The model predicts the system at every horizon

  One-step commutation lifts to n steps: a correct simple model is a correct
  predictor at any depth. The #11 counterpart of `InternalModel.tracks`. -/

theorem Understanding.tracks {S M : Type*} (u : Understanding S M) (n : ℕ) (s : S) :
    u.abstract (u.systemDyn^[n] s) = u.modelDyn^[n] (u.abstract s) := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih (u.systemDyn s), u.abstracts,
        ← Function.iterate_succ_apply]

/-- The simple model's n-step prediction from a system state. -/
def Understanding.predict {S M : Type*} (u : Understanding S M) (n : ℕ) (s : S) : M :=
  u.modelDyn^[n] (u.abstract s)

/-- Anticipation through compression: running the simple model forward n steps from
    a coarse-grained state equals the system's true n-step future, coarse-grained.
    Understanding the comprehensible law (`modelDyn`) is enough to predict the
    incomprehensibly detailed system. -/
theorem Understanding.predict_correct {S M : Type*} (u : Understanding S M)
    (n : ℕ) (s : S) :
    u.predict n s = u.abstract (u.systemDyn^[n] s) :=
  (u.tracks n s).symm

/-- Understanding preserves rest: a system equilibrium coarse-grains to a model
    equilibrium. The simple model agrees with the system about what stands still. -/
theorem Understanding.equilibrium_image {S M : Type*} (u : Understanding S M)
    {s : S} (h : IsEquilibrium u.systemDyn s) :
    IsEquilibrium u.modelDyn (u.abstract s) := by
  unfold IsEquilibrium at *
  rw [← u.abstracts, h]

/-! ## The model is strictly smaller — the quantitative face (bridge to #7)

  On finite carriers, an onto + lossy abstraction has a strictly smaller codomain,
  hence strictly lower Hartley nonspecificity. "Simpler than the modelled" is not just
  structural (non-injective) but measurable (fewer states, less log-count). -/

/-- An understanding's model space has strictly fewer states than the system: a
    surjection that is not injective drops cardinality. -/
theorem Understanding.card_lt {S M : Type*} [Fintype S] [Fintype M]
    (u : Understanding S M) : Fintype.card M < Fintype.card S := by
  rcases lt_or_eq_of_le (Fintype.card_le_of_surjective _ u.surjective) with h | h
  · exact h
  · exact absurd
      ((Fintype.bijective_iff_surjective_and_card u.abstract).mpr ⟨u.surjective, h.symm⟩).injective
      u.compresses

/-- Understanding strictly lowers Hartley nonspecificity (#7): the model resolves
    strictly fewer distinguishable states than the system. This is the information-
    theoretic statement of "the model is simpler" — `hartley = log (card)`, and the
    card drops, so the log drops. The compression of #11 is the Hartley drop of #7. -/
theorem Understanding.hartley_lt {S M : Type*} [Fintype S] [Fintype M]
    (u : Understanding S M) :
    hartley (Finset.univ : Finset M) < hartley (Finset.univ : Finset S) := by
  rw [hartley, hartley, Finset.card_univ, Finset.card_univ]
  apply Real.log_lt_log
  · haveI := u.nontrivial
    haveI : Nonempty M := ⟨(exists_pair_ne M).choose⟩
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card M)
  · exact_mod_cast u.card_lt

/-! ## Modeling is trivial; understanding is not — independence of #11 from #9

  Every system models itself (the identity InternalModel always exists). Two witnesses
  show this is not enough for understanding: a one-state system (nothing to compress)
  and a three-state system with prime-cyclic dynamics (compression forbidden). -/

/-- The trivial self-model: every system with dynamics `f` is an InternalModel of
    itself, with the identity as the modelling map. Witnesses that #9 is always
    satisfiable — modeling, in the bare sense, costs nothing. -/
def InternalModel.refl {S : Type*} (f : S → S) : InternalModel S S where
  model := id
  internalDyn := f
  systemDyn := f
  simulates := fun _ => rfl

/-- The identity map is not an understanding. The model that duplicates the system
    state-for-state simplifies nothing, so it cannot satisfy `compresses`: even a
    perfect, full-resolution model of a system is not yet an understanding of it. -/
theorem no_trivial_understanding {S : Type*} (u : Understanding S S)
    (h : u.abstract = id) : False := by
  apply u.compresses
  rw [h]
  exact Function.injective_id

/-- No subsingleton system can be understood: with at most one state there is nothing
    to collapse, so every abstraction out of it is injective and fails `compresses`.
    Understanding needs something to throw away. -/
theorem no_understanding_of_subsingleton {S M : Type*} [Subsingleton S]
    (u : Understanding S M) : False :=
  u.compresses (fun a b _ => Subsingleton.elim a b)

/-- **Independence witness I (minimal): #9 ⇏ #11.** A one-state system has an internal
    model (every system does — `InternalModel.refl`) yet admits NO understanding for any
    model space (`no_understanding_of_subsingleton`, since `Unit` is a subsingleton).
    "Has a model" is satisfied while "is understood" is impossible. -/
theorem modeling_does_not_imply_understanding :
    (∃ _ : InternalModel Unit Unit, True) ∧ (∀ M, Understanding Unit M → False) :=
  ⟨⟨InternalModel.refl id, trivial⟩, fun _ u => no_understanding_of_subsingleton u⟩

/-! ## The stronger witness: dynamics-incompressibility

  A three-state system whose dynamics is the 3-cycle `x ↦ x + 1`. It has a model, but
  it cannot be understood — not because there is nothing to compress (it has three
  states), but because 3 is prime: the only equivalence on its states that respects the
  dynamics, short of the diagonal, is the all-collapse, and that is exactly the
  degenerate total collapse `nontrivial` forbids. Understanding is impossible despite
  ample room — the dynamics themselves are incompressible. -/

/-- A three-state system with the 3-cycle as its dynamics cannot be understood. Any
    abstraction respecting the dynamics that identifies two of the three states is
    forced (because the cycle visits all three) to identify all three, collapsing the
    model to a point and violating `nontrivial`. -/
theorem cyclic3_no_understanding {M : Type*} (u : Understanding (Fin 3) M)
    (h : ∀ x : Fin 3, u.systemDyn x = x + 1) : False := by
  -- the kernel of `abstract` is a congruence for the +1 dynamics
  have hstep : ∀ a b : Fin 3, u.abstract a = u.abstract b →
      u.abstract (a + 1) = u.abstract (b + 1) := by
    intro a b hab
    have ea : u.abstract (a + 1) = u.modelDyn (u.abstract a) := by
      have e := u.abstracts a; rw [h a] at e; exact e
    have eb : u.abstract (b + 1) = u.modelDyn (u.abstract b) := by
      have e := u.abstracts b; rw [h b] at e; exact e
    rw [ea, eb, hab]
  -- a genuine identification from compression
  obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp u.compresses
  -- closed decidable arithmetic over Fin 3
  have hd : ∀ x y : Fin 3, x ≠ y → (y = x + 1 ∨ y = x + 2) := by decide
  have c1 : ∀ x : Fin 3, x + 2 + 1 = x := by decide
  have c2 : ∀ x : Fin 3, x + 1 + 1 = x + 2 := by decide
  have cover : ∀ x y : Fin 3, y = x ∨ y = x + 1 ∨ y = x + 2 := by decide
  -- one generator edge: abstract a = abstract (a+1)
  have g : u.abstract a = u.abstract (a + 1) := by
    rcases hd a b hne with hb | hb
    · rw [hb] at hab; exact hab
    · have e := hstep a b hab
      rw [hb, c1 a] at e
      exact e.symm
  -- second edge: abstract (a+1) = abstract (a+2)
  have g2 : u.abstract (a + 1) = u.abstract (a + 2) := by
    have e := hstep a (a + 1) g
    rw [c2 a] at e
    exact e
  -- abstract is constant — every state maps to abstract a
  have alleq : ∀ x : Fin 3, u.abstract x = u.abstract a := by
    intro x
    rcases cover a x with hx | hx | hx
    · rw [hx]
    · rw [hx]; exact g.symm
    · rw [hx]; exact g2.symm.trans g.symm
  -- constant abstract contradicts surjectivity onto a nontrivial M
  haveI := u.nontrivial
  obtain ⟨m₁, m₂, hm⟩ := exists_pair_ne M
  obtain ⟨x₁, hx₁⟩ := u.surjective m₁
  obtain ⟨x₂, hx₂⟩ := u.surjective m₂
  exact hm (by rw [← hx₁, ← hx₂, alleq x₁, alleq x₂])

/-- **Independence witness II (strong): #9 ⇏ #11 even for richly dynamic systems.** The
    3-cycle on three states has an internal model yet admits no understanding. Modeling
    is free; understanding can be impossible even when there is plenty to compress —
    the obstruction is the dynamics, not the cardinality. -/
theorem cyclic3_modeling_not_understanding :
    (∃ _ : InternalModel (Fin 3) (Fin 3), True) ∧
      (∀ (M : Type) (u : Understanding (Fin 3) M),
        (∀ x : Fin 3, u.systemDyn x = x + 1) → False) :=
  ⟨⟨InternalModel.refl (fun x => x + 1), trivial⟩,
    fun _ u h => cyclic3_no_understanding u h⟩

/-! ## Understanding is non-vacuous

  A concrete understandable system: S = Bool × Bool whose first coordinate is a
  conserved quantity and whose second is irrelevant churn. The understanding keeps the
  predictable invariant and discards the noise — exactly what understanding does. -/

/-- A system with a conserved coordinate and a noisy one. `abstract = fst` throws away
    the noise; the resulting one-state-dynamics `id` captures the law "the invariant is
    invariant." Surjective, strictly lossy, and the model `Bool` is non-degenerate, so a
    genuine Understanding exists. -/
def noisyPairUnderstanding : Understanding (Bool × Bool) Bool where
  abstract := Prod.fst
  systemDyn := fun p => (p.1, !p.2)
  modelDyn := id
  abstracts := fun _ => rfl
  surjective := fun b => ⟨(b, false), rfl⟩
  compresses := by
    intro hinj
    have h : ((true, true) : Bool × Bool) = (true, false) :=
      hinj (show ((true, true) : Bool × Bool).1 = ((true, false) : Bool × Bool).1 from rfl)
    exact absurd h (by decide)
  nontrivial := inferInstance

end Systems
