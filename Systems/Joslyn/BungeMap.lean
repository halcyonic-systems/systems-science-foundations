/-
  Systems/Joslyn/BungeMap.lean
  Phase 4.4: the Joslyn→Bunge partial map — the NON-FUNCTORIAL edge

  Joslyn's environment is DERIVED (Def 21: the constraint C = X − S is what
  the act of distinction excludes); Bunge's is PRIMITIVE (E is given in the
  CES triple, constrained only by C ∩ E = ∅). The map from Joslyn systems to
  Bunge systems therefore exists only relative to externally supplied data —
  it is a structure-preserving map, not a functor.

  TWO seams, not one (the second found in the 2026-07-11 sketch session):
  1. ENVIRONMENT (roadmap §4.4): Bunge's E must be chosen; Joslyn determines
     no canonical element-level environment beyond the support complement.
  2. BONDAGE (action semantics): Bunge Def 1.1 demands two distinct BONDED
     components, but Joslyn Def 5 states are pure relation — no action
     semantics. `ActsOn` evidence must also be supplied externally.

  Results:
  - `toBunge` — the partial map, both seams as explicit hypotheses
  - `toBunge_ne_of_env_ne` + `joslyn_toBunge_not_canonical` — the
    non-functoriality witness: one Joslyn system, two admissible
    environments, two different Bunge systems
  - `toBungeDerived` + `toBungeDerived_subsystem` — the conditional result:
    if E is DERIVED (env := supportᶜ, Joslyn-style), the assignment is
    canonical and monotone from states-inclusion into Bunge's Subsystem
    partial order — a functor between the poset categories. The roadmap's
    "would be a functor if Bunge's environment were derived", machine-checked.
-/

import Systems.Core.System
import Systems.Joslyn.JoslynSystem

namespace Systems

/-! ## The support — carrier discipline for the map

  Joslyn states live in `Set (α × α)`; Bunge's composition and environment
  live in `Set α`. The composition of the image system is the SUPPORT: the
  elements that appear in some constrained state. -/

/-- The support of a binary Joslyn system: elements appearing in some
    constrained state. This is the composition of any Bunge image — the
    things the distinction is actually about. -/
def JoslynSystem₂.support {α : Type*} (J : JoslynSystem₂ α) : Set α :=
  {a | ∃ b, (a, b) ∈ J.states ∨ (b, a) ∈ J.states}

/-- Support is monotone in the constrained states. -/
theorem JoslynSystem₂.support_mono {α : Type*} {J₁ J₂ : JoslynSystem₂ α}
    (h : J₁.states ⊆ J₂.states) : J₁.support ⊆ J₂.support := by
  rintro a ⟨b, hab | hba⟩
  · exact ⟨b, Or.inl (h hab)⟩
  · exact ⟨b, Or.inr (h hba)⟩

/-! ## The partial map -/

/-- The Joslyn→Bunge partial map (roadmap §4.4). NOT a functor: beyond the
    Joslyn system itself it requires TWO externally supplied pieces of data,
    one per ontological seam:

    * `env` + `hdisj` — Bunge's environment is PRIMITIVE; Joslyn's is derived
      from the distinction. No canonical choice exists (see
      `joslyn_toBunge_not_canonical`), so E must be given.
    * `hbond` — Bunge Def 1.1 requires at least two distinct bonded
      components; Joslyn's relational states carry no action semantics, so
      bondage evidence must be given.

    The composition is the support, the structure is the constrained states
    themselves. -/
def JoslynSystem₂.toBunge {α : Type*} [ActsOn α] (J : JoslynSystem₂ α)
    (env : Set α)
    (hdisj : J.support ∩ env = ∅)
    (hbond : ∃ a ∈ J.support, ∃ b ∈ J.support, a ≠ b ∧ Bonded a b) :
    ConcreteSystem α where
  composition := J.support
  environment := env
  structure' := J.states
  disjoint := hdisj
  structure_on := fun p hp =>
    ⟨Or.inl ⟨p.2, Or.inl hp⟩, Or.inl ⟨p.1, Or.inr hp⟩⟩
  bondage_nonempty := hbond

/-! ## Non-functoriality: the environment is not determined by J -/

/-- Different environment choices give DIFFERENT Bunge systems from the same
    Joslyn system — the map is not a function of `J` alone. -/
theorem JoslynSystem₂.toBunge_ne_of_env_ne {α : Type*} [ActsOn α]
    (J : JoslynSystem₂ α) {env₁ env₂ : Set α}
    (h₁ : J.support ∩ env₁ = ∅) (h₂ : J.support ∩ env₂ = ∅)
    (b₁ : ∃ a ∈ J.support, ∃ b ∈ J.support, a ≠ b ∧ Bonded a b)
    (b₂ : ∃ a ∈ J.support, ∃ b ∈ J.support, a ≠ b ∧ Bonded a b)
    (hne : env₁ ≠ env₂) :
    J.toBunge env₁ h₁ b₁ ≠ J.toBunge env₂ h₂ b₂ := by
  intro h
  exact hne (congrArg ConcreteSystem.environment h)

section Witness

/-- Action evidence for the witness carrier: everything acts on everything.
    Local to this section — the witness needs SOME `ActsOn`, and the
    obstruction being exhibited is environmental, not action-theoretic. -/
local instance : ActsOn (Fin 3) := ⟨fun _ _ => True⟩

/-- The witness Joslyn system: one constrained state, `(0, 1)`. Support is
    `{0, 1}`, leaving `2` available as a genuine environment element. -/
private def witnessJ : JoslynSystem₂ (Fin 3) where
  states := {((0 : Fin 3), (1 : Fin 3))}
  nonempty := ⟨(0, 1), rfl⟩

private theorem witnessJ_support : witnessJ.support = {0, 1} := by
  ext a
  constructor
  · rintro ⟨b, hab | hba⟩
    · simp only [witnessJ, Set.mem_singleton_iff, Prod.ext_iff] at hab
      exact Or.inl hab.1
    · simp only [witnessJ, Set.mem_singleton_iff, Prod.ext_iff] at hba
      exact Or.inr hba.2
  · rintro (rfl | rfl)
    · exact ⟨1, Or.inl rfl⟩
    · exact ⟨0, Or.inr rfl⟩

/-- THE NON-FUNCTORIALITY WITNESS (roadmap §4.6 item 3): a single Joslyn
    system admitting two environments — the empty one and `{2}` — whose Bunge
    images differ. Environment-as-derived vs environment-as-primitive is a
    genuine ontological disagreement: no assignment of Bunge systems to
    Joslyn systems can be canonical in the environment. -/
theorem joslyn_toBunge_not_canonical :
    ∃ (J : JoslynSystem₂ (Fin 3)) (env₁ env₂ : Set (Fin 3))
      (h₁ : J.support ∩ env₁ = ∅) (h₂ : J.support ∩ env₂ = ∅)
      (hb : ∃ a ∈ J.support, ∃ b ∈ J.support, a ≠ b ∧ Bonded a b),
      J.toBunge env₁ h₁ hb ≠ J.toBunge env₂ h₂ hb := by
  have hdisj₂ : witnessJ.support ∩ {2} = ∅ := by
    rw [witnessJ_support]
    ext a
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, iff_false, not_and]
    rintro (rfl | rfl) <;> decide
  have hb : ∃ a ∈ witnessJ.support, ∃ b ∈ witnessJ.support,
      a ≠ b ∧ Bonded a b := by
    refine ⟨0, ?_, 1, ?_, ?_, Or.inl trivial⟩
    · rw [witnessJ_support]; exact Or.inl rfl
    · rw [witnessJ_support]; exact Or.inr rfl
    · decide
  -- ∅ ≠ {2} proved at the membership level: Set.Nonempty.ne_empty routes
  -- through Classical.choice in Mathlib (incidental, run-4 pattern)
  have henv : (∅ : Set (Fin 3)) ≠ ({2} : Set (Fin 3)) := by
    intro h
    have h2 : (2 : Fin 3) ∈ ({2} : Set (Fin 3)) := rfl
    rw [← h] at h2
    exact h2
  exact ⟨witnessJ, ∅, {2}, Set.inter_empty _, hdisj₂, hb,
    witnessJ.toBunge_ne_of_env_ne _ _ hb hb henv⟩

end Witness

/-! ## The conditional result: derived environment restores functoriality

  If Bunge's E were DERIVED the way Joslyn's constraint is — everything the
  distinction leaves out, `env := supportᶜ` — the assignment becomes
  canonical (a function of J alone) and monotone into Bunge's Subsystem
  partial order. A monotone map of posets IS a functor of the corresponding
  categories: this is the precise content of the roadmap's "the map would be
  a functor if Bunge's environment were derived". -/

/-- `support ∩ supportᶜ = ∅`, proved at the membership level.
    Mathlib's `Set.inter_compl_self` routes through `Classical.choice`
    (incidental, run-4 pattern); the fact itself is constructive. -/
theorem JoslynSystem₂.support_inter_compl {α : Type*} (J : JoslynSystem₂ α) :
    J.support ∩ J.supportᶜ = ∅ :=
  Set.ext fun _ => ⟨fun h => (h.2 h.1).elim, False.elim⟩

/-- The canonical map obtained by DERIVING the environment Joslyn-style:
    `env := supportᶜ`. Only the bondage seam remains as an input. -/
def JoslynSystem₂.toBungeDerived {α : Type*} [ActsOn α] (J : JoslynSystem₂ α)
    (hbond : ∃ a ∈ J.support, ∃ b ∈ J.support, a ≠ b ∧ Bonded a b) :
    ConcreteSystem α :=
  J.toBunge J.supportᶜ J.support_inter_compl hbond

/-- CONDITIONAL FUNCTORIALITY: with the environment derived, the assignment
    is monotone from states-inclusion into Bunge's Subsystem order — larger
    distinction, larger composition, SMALLER environment (the complement),
    larger structure. Exactly the C ⊆ / E ⊇ / S ⊆ shape of Def 1.6.

    Note the environment leg is the CONSTRUCTIVE complement direction
    (`a ∉ support₂ → a ∉ support₁`), not double-negation elimination — unlike
    Def 21's `compl_constraint`, this theorem is expected axiom-free. -/
theorem JoslynSystem₂.toBungeDerived_subsystem {α : Type*} [ActsOn α]
    {J₁ J₂ : JoslynSystem₂ α} (h : J₁.states ⊆ J₂.states)
    (b₁ : ∃ a ∈ J₁.support, ∃ b ∈ J₁.support, a ≠ b ∧ Bonded a b)
    (b₂ : ∃ a ∈ J₂.support, ∃ b ∈ J₂.support, a ≠ b ∧ Bonded a b) :
    Subsystem (J₁.toBungeDerived b₁) (J₂.toBungeDerived b₂) :=
  ⟨JoslynSystem₂.support_mono h,
   fun _ ha hmem => ha (JoslynSystem₂.support_mono h hmem),
   h⟩

end Systems
