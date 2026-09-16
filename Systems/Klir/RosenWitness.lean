/-
  Systems/Klir/RosenWitness.lean
  Mapping 008, claim 3: a Bunge concrete system whose Rosen view loses the bond

  The witness owed by atlas/mappings/rosen-arrow.md: "a Bunge concrete
  system (two bonded things) whose Rosen view is a single state set with
  observables, i.e. the bond is not recoverable from (S, F)". Two
  witnesses, one per face of Bunge's bond (Bond.lean: "bonding is
  symmetric but ActsOn is not — the asymmetry (agent vs. patient) is
  important").

  (1) DIRECTED BOND, NO VIEW. `false` acts on `true` and nothing acts
      back (Bunge's a ▷ b). The concrete system has that one action as
      its structure. Its (T, R) is asymmetric, so by
      `rosen_no_view_of_asymmetric` no Rosen pair whatever projects to
      it. The agent/patient direction Bunge insists on has no home in
      (S, F).

  (2) MUTUAL BOND, ONE REDUCED STATE. Both act on each other (and each
      on itself, so the dependency is an equivalence and the view
      exists). The generated Rosen view has exactly ONE observable, the
      constant 1, and its two states are indistinguishable: S/R_F is a
      point. The bond survives only as loss of resolution — Rosen sees
      "bonded" as "not separable by any observable", never as a relation
      between two things. Bunge's Def 1.1 needs a ≠ b; the view has no
      way to say there are two.

  Neither witness is a defect of the encoding: `RosenSystem.indist_symm`
  is Rosen's R_F, and R_F is all a pair (S, F) determines.
-/

import Systems.Klir.ViewGeneration

namespace Systems

namespace RosenWitness

/-- Two things; `false` acts on `true`, nothing acts on `false`. -/
scoped instance : ActsOn Bool := ⟨fun a b => a = false ∧ b = true⟩

theorem false_acts_true : actsOn false true := ⟨rfl, rfl⟩

/-- Witness (1): Bunge concrete system with a single directed bond. -/
def directedPair : ConcreteSystem Bool where
  composition := Set.univ
  environment := ∅
  structure' := {(false, true)}
  disjoint := Set.inter_empty _
  structure_on := by
    rintro p hp
    exact ⟨Or.inl (Set.mem_univ _), Or.inl (Set.mem_univ _)⟩
  bondage_nonempty :=
    ⟨false, Set.mem_univ _, true, Set.mem_univ _, Bool.false_ne_true, Or.inl false_acts_true⟩

/-- The directed pair as a kernel (its (T, R) with the arrow proof). -/
def directedKernel : Kernel Bool where
  things := Set.univ
  dep := {(false, true)}
  dep_on := fun _ _ => ⟨Set.mem_univ _, Set.mem_univ _⟩

theorem directedPair_toKlir : directedPair.toKlir = directedKernel.toKlir := rfl

/-- CLAIM 3, DIRECTED FACE: no Rosen pair projects to the bonded pair's
    (T, R). The bond `false ▷ true` is unrecoverable because it is
    one-way and every R_F is symmetric. -/
theorem directedPair_has_no_rosen_view :
    ∀ V : RosenSystem Bool, V.toKlir ≠ directedPair.toKlir := by
  rw [directedPair_toKlir]
  apply rosen_no_view_of_asymmetric
  refine ⟨(false, true), rfl, ?_⟩
  simp [directedKernel]

/-- Witness (2): the mutually bonded pair as a kernel — the full relation. -/
def mutualKernel : Kernel Bool where
  things := Set.univ
  dep := Set.univ
  dep_on := fun _ _ => ⟨Set.mem_univ _, Set.mem_univ _⟩

theorem mutualKernel_isIndist : mutualKernel.IsIndist where
  refl := fun _ _ => Set.mem_univ _
  symm := fun _ _ => Set.mem_univ _
  trans := fun _ _ _ _ _ => Set.mem_univ _

theorem mutualKernel_hasBond : mutualKernel.HasBond :=
  ⟨(false, true), Set.mem_univ _, Bool.false_ne_true, Or.inl false_acts_true⟩

/-- The Bunge view of the mutual pair exists (two bonded components). -/
noncomputable def mutualBunge : ConcreteSystem Bool :=
  mutualKernel.toBunge mutualKernel_hasBond

/-- The Rosen view of the same kernel exists. -/
noncomputable def mutualRosen : RosenSystem Bool :=
  mutualKernel.toRosen mutualKernel_isIndist

/-- CLAIM 3, MUTUAL FACE (i): the Rosen view has exactly one observable,
    the constant 1 — "a single state set with observables". -/
theorem mutualRosen_observables : mutualRosen.observables = {fun _ => (1 : ℝ)} := by
  ext f
  simp only [mutualRosen, Kernel.toRosen, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, -, rfl⟩
    funext x
    exact mutualKernel.classIndicator_eq_one (Set.mem_univ _)
  · rintro rfl
    refine ⟨false, Set.mem_univ _, ?_⟩
    funext x
    exact (mutualKernel.classIndicator_eq_one (Set.mem_univ _)).symm

/-- CLAIM 3, MUTUAL FACE (ii): the two bonded things are one reduced
    state — no observable separates them. Bunge's a ≠ b is invisible. -/
theorem mutualRosen_indist_false_true : (false, true) ∈ mutualRosen.indist := by
  refine ⟨Set.mem_univ _, Set.mem_univ _, ?_⟩
  intro f hf
  rw [mutualRosen_observables, Set.mem_singleton_iff] at hf
  subst hf
  rfl

end RosenWitness

end Systems
