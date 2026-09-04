/-
  Systems/Principles/Hierarchy.lean — #2 Hierarchy re-headlined on Mobus Eq. 4.3.

  WHY THIS FILE. The independence matrix (Matrix.lean, docs/paper/independence-matrix.md)
  ran #2 on `ImmediateAncestor α`, a class with one Prop-valued relation and no law. It is
  inhabited on every carrier by the empty relation, so "no #2-instance exists" is never true
  and both A ⇏ #2 cells were recorded as derivations into a vacuous target. The reading
  edition's ledger (p3-reading-edition.md, "showcase structure only") notes that Level.lean
  also holds Mobus's own definition, Eq. 4.3 (`RecursiveComponent`), and Simon's content
  (`NearDecomposable`). This file headlines #2 on those and recomputes the component block.

  THE PREDICATE. `Hierarchical σ T` (below) says: a concrete system `σ` admits a Mobus
  decomposition tree whose atoms are exactly its components, with a genuine subsystem level,
  every complex node a system in its own right (Eq. 4.3's `c = S_{l+1}`), sibling atom-sets
  disjoint, and the top-level modules near-decomposable in Simon's sense (Level.lean's
  `NearDecomposable`, within ≥ threshold > between). It is NOT vacuous: `not_hierarchical_of_
  uniform` shows that under a uniform interaction strength no system on any carrier is
  hierarchical, and `twoLevelHierarchical` shows a two-level system that is.

  THE CHOICE, documented. Of the two content conditions offered (a `NearDecomposable`
  instance, or acyclicity of `ImmediateAncestor`), this file takes near-decomposability.
  Reason: Eq. 4.3 and Mobus's sentence at 2-principles-of-systems-science.md:287 ("component
  interactions within the subsystem are stronger than interactions between components in
  other subsystems") are the same claim seen from structure and from strength; acyclicity of
  a bare ancestry relation is Bunge's descent order and says nothing about strength. The
  price is one extra ambient instance, `InteractionStrength α T`, exactly as #1 has `ActsOn`.
  Hierarchy so encoded is a property of the strength profile: `twoLevel` below is
  hierarchical under a graded profile (`gradedStrength`) and not under the uniform one
  (`sep_systemness_hierarchical`), with the bond graph unchanged.

  BRIDGES THAT HAD TO BE DEFINED. `RecursiveComponent` carries no relation to `ActsOn` or
  to `ConcreteSystem`: it has a `thing` label per node and a child list, nothing else. Three
  definitions bridge it: `atoms` / `atomSet` (the leaf things, so "atoms are the components"
  is `atomSet = composition`); `modules` (the children's atom-sets, so Simon's partition is
  the tree's top level); and `IsDecomposition` (the per-node conditions that make the tree a
  decomposition rather than an arbitrary labelled tree: ≥ 2 children, disjoint siblings,
  organized atoms). Note that the `thing` label of a complex node is dead data for all of
  this: the carrier has no element that IS the subsystem, so `twoLevel` labels its subsystem
  with an arbitrary component. `InteractionStrength` likewise carries no relation to
  `ActsOn`, so `organized` (bonds) and `nd` (strengths) are independent bridges to #1's and
  Simon's vocabularies; neither implies the other.

  THE SIX CELLS, recomputed (row A has an instance, column B has none; convention of
  Matrix.lean). Old verdict → new verdict:
    (#1,#2)  D into a vacuous target  →  W `sep_systemness_hierarchical` (substantive: the
             uniform-strength profile, on the very system that is hierarchical under a graded
             one; ᵃ in the strength) and Wᶜ `sep_systemness_hierarchical_bool` (any strength,
             any action, on a two-thing carrier).
    (#2,#1)  Wᵃ / Wᶜ (ancestry without bonds)  →  NOT SEPARABLE, by construction:
             `Hierarchical` is indexed by the system it decomposes
             (`Hierarchical.toConcreteSystem`). This is Eq. 4.3 itself: a complex component IS
             a system, so hierarchy presupposes systemness. The old witnesses had no bonds
             because `ImmediateAncestor` had no bonds to require.
    (#2,#3)  Wᶜ (reflexive self-ancestry has no flow)  →  NOT SEPARABLE:
             `Hierarchical.toFlowNetwork`, edges nonempty via #1's derivation.
    (#3,#2)  D into a vacuous target  →  W `sep_networks_hierarchical` (uniform strength;
             choice-free in the action relation, ᵃ in the strength).
    (#1,#3), (#3,#1): unchanged, they do not mention #2 (Matrix.lean).

  PROPOSED REPLACEMENT for `principle2_hierarchy` in Systems/Principles.lean (NOT applied
  here; Principles.lean is untouched). Current text:

    /-- **#2 Hierarchy** (axiom, `ImmediateAncestor`, Level.lean). The ancestor relation is
        transitive: levels stack. -/
    theorem principle2_hierarchy {α : Type*} [ImmediateAncestor α] {x y z : α}
        (hxz : Ancestor x z) (hzy : Ancestor z y) : Ancestor x y :=
      ancestor_trans hxz hzy

  Proposed text:

    /-- **#2 Hierarchy** (axiom, `RecursiveComponent` + `NearDecomposable`, Level.lean;
        predicate `Hierarchical`, Principles/Hierarchy.lean). Mobus Eq. 4.3:
          c_{i,j,l} = S_{i,j,l+1}  if component is complex
                      c_a            if component is atomic
        A hierarchical system has a subsystem level, every complex component is a system, and
        within-module interaction exceeds between-module interaction. Levels stack, and the
        stacking has content: under a uniform interaction strength no system is hierarchical
        (`not_hierarchical_of_uniform`), and a hierarchical system has at least three
        components in at least two modules (`Hierarchical.exists_split`). -/
    theorem principle2_hierarchy {α : Type*} [ActsOn α] {σ : ConcreteSystem α}
        {T : Type*} [LinearOrder T] [InteractionStrength α T] (h : Hierarchical σ T) :
        2 ≤ h.tree.depth ∧
          ∃ m₁ ∈ h.nd.modules, ∃ m₂ ∈ h.nd.modules, m₁ ≠ m₂ ∧
            ∀ x ∈ m₁, ∀ y ∈ m₁, x ≠ y → ∀ z ∈ m₂,
              @strength α T _ x z < @strength α T _ x y :=
      ⟨h.two_le_depth, h.within_exceeds_between_somewhere⟩

  Every theorem below records its `#print axioms` profile in its docstring (kernel output,
  2026-09-04). None uses `sorryAx`. All but `List.exists_rel_of_pairwise` show
  {propext, Classical.choice, Quot.sound}; `Classical.choice` enters through the definition
  `RecursiveComponent.atoms` itself (nested structural recursion over `List`, checked:
  `#print axioms RecursiveComponent.atoms`), so every statement mentioning `atomSet`
  inherits it regardless of proof content. Level.lean's `depth` shows {propext, Quot.sound}.
-/
import Systems.Principles.Matrix

namespace Systems

open RecursiveComponent

/-! ## Bridges from `RecursiveComponent` to the component vocabulary -/

/-- The children of a node (empty for an atom). -/
def RecursiveComponent.children {α : Type*} :
    RecursiveComponent α → List (RecursiveComponent α)
  | .atomic _ => []
  | .complex _ cs => cs

/-- Whether a node is complex (has a child list). -/
def RecursiveComponent.IsComplex {α : Type*} : RecursiveComponent α → Prop
  | .atomic _ => False
  | .complex _ _ => True

/-- The atoms of a tree, as a list: the `thing`s at its leaves, left to right. The `thing`
    labels of complex nodes do not appear. This is the bridge from Eq. 4.3 to "the
    components of the system". -/
def RecursiveComponent.atoms {α : Type*} : RecursiveComponent α → List α
  | .atomic a => [a]
  | .complex _ cs => cs.foldr (fun c acc => c.atoms ++ acc) []

/-- The atoms of a tree as a set. -/
def RecursiveComponent.atomSet {α : Type*} (t : RecursiveComponent α) : Set α :=
  {a | a ∈ t.atoms}

/-- The top-level modules of a tree: the atom-sets of its children. This is the bridge from
    Eq. 4.3 to Simon's partition (`NearDecomposable.modules`). -/
def RecursiveComponent.modules {α : Type*} (t : RecursiveComponent α) : List (Set α) :=
  t.children.map RecursiveComponent.atomSet

theorem RecursiveComponent.mem_atoms_complex {α : Type*} {a : α} {b : α}
    {cs : List (RecursiveComponent α)} :
    a ∈ (RecursiveComponent.complex b cs).atoms ↔ ∃ c ∈ cs, a ∈ c.atoms := by
  simp only [RecursiveComponent.atoms]
  induction cs with
  | nil => simp
  | cons c cs ih => simp [List.foldr_cons, List.mem_append]

/-- A tree is a Mobus decomposition when every complex node has at least two children
    (a subsystem is not a renaming of one component), sibling atom-sets are pairwise disjoint
    (each component sits in exactly one subsystem per level), and the node's atoms are
    organized (`IsOrganized`: a bonded pair of distinct things — Eq. 4.3's `c = S_{l+1}`,
    the complex component is itself a system in the sense of #1). -/
inductive RecursiveComponent.IsDecomposition {α : Type*} [ActsOn α] :
    RecursiveComponent α → Prop
  | atomic (a : α) : IsDecomposition (.atomic a)
  | complex (a : α) (cs : List (RecursiveComponent α))
      (branching : 2 ≤ cs.length)
      (disjoint : (cs.map RecursiveComponent.atomSet).Pairwise Disjoint)
      (organized : IsOrganized (RecursiveComponent.complex a cs).atomSet)
      (children : ∀ c ∈ cs, IsDecomposition c) :
      IsDecomposition (.complex a cs)

/-! ## The predicate -/

/-- **#2 Hierarchy, re-headlined.** A concrete system `σ` is hierarchical (relative to an
    interaction-strength profile `strength : α → α → T`) when it admits a Mobus decomposition
    tree (Eq. 4.3) whose atoms are exactly its components, with at least one complex child
    (a genuine subsystem level, so `2 ≤ tree.depth` by `two_le_depth`), and whose top-level
    modules are near-decomposable in Simon's sense (Level.lean's `NearDecomposable`:
    within-module strength ≥ threshold > between-module strength).

    The ambient `InteractionStrength α T` plays for #2 the role `ActsOn α` plays for #1.
    Nothing ties the two: see `not_hierarchical_of_uniform` (fails for every action relation)
    and `twoLevelHierarchical` (holds under one graded profile). -/
structure Hierarchical {α : Type*} [ActsOn α] (σ : ConcreteSystem α) (T : Type*)
    [LinearOrder T] [InteractionStrength α T] where
  /-- The decomposition tree (Mobus Eq. 4.3) -/
  tree : RecursiveComponent α
  /-- Its atoms are exactly the components -/
  atoms_eq : tree.atomSet = σ.composition
  /-- Some child is itself complex: there is a subsystem level -/
  nested : ∃ c ∈ tree.children, c.IsComplex
  /-- The tree is a decomposition, not an arbitrary labelled tree -/
  decomposition : tree.IsDecomposition
  /-- Simon's near-decomposability of `σ` -/
  nd : NearDecomposable σ T
  /-- ... whose modules are the tree's top-level modules -/
  modules_eq : nd.modules = tree.modules

/-! ## Structure lemmas -/

theorem RecursiveComponent.foldl_max_depth_ge_init {α : Type*}
    (l : List (RecursiveComponent α)) (init : ℕ) :
    init ≤ l.foldl (fun acc c => max acc c.depth) init := by
  induction l generalizing init with
  | nil => exact le_refl _
  | cons c cs ih => exact le_trans (le_max_left _ _) (ih _)

theorem RecursiveComponent.foldl_max_depth_ge_mem {α : Type*}
    {l : List (RecursiveComponent α)} {c : RecursiveComponent α} (hc : c ∈ l) (init : ℕ) :
    c.depth ≤ l.foldl (fun acc c => max acc c.depth) init := by
  induction l generalizing init with
  | nil => exact absurd hc (List.not_mem_nil)
  | cons d ds ih =>
    rcases List.mem_cons.mp hc with rfl | hmem
    · exact le_trans (le_max_right _ _) (RecursiveComponent.foldl_max_depth_ge_init ds _)
    · exact ih hmem _

/-- A complex child forces depth at least two.
    `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem Hierarchical.two_le_depth {α : Type*} [ActsOn α] {σ : ConcreteSystem α}
    {T : Type*} [LinearOrder T] [InteractionStrength α T] (h : Hierarchical σ T) :
    2 ≤ h.tree.depth := by
  obtain ⟨c, hc, hcomplex⟩ := h.nested
  match ht : h.tree, c, hcomplex with
  | .atomic _, _, _ =>
    rw [ht] at hc
    exact absurd hc (List.not_mem_nil)
  | .complex a cs, .atomic _, hcx => exact hcx.elim
  | .complex a cs, .complex b ds, _ =>
    rw [ht] at hc
    simp only [RecursiveComponent.children] at hc
    have h1 : 1 ≤ (RecursiveComponent.complex b ds).depth := by
      simp [RecursiveComponent.depth]
    have h2 := RecursiveComponent.foldl_max_depth_ge_mem hc 0
    simp only [RecursiveComponent.depth]
    omega

/-- A decomposition has an atom (the childless complex node is excluded by `branching`).
    `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem RecursiveComponent.IsDecomposition.exists_atom {α : Type*} [ActsOn α] :
    ∀ {t : RecursiveComponent α}, t.IsDecomposition → ∃ a, a ∈ t.atoms
  | .atomic a, _ => ⟨a, by simp [RecursiveComponent.atoms]⟩
  | .complex _ cs, .complex _ _ hb _ _ hch => by
    match cs, hb, hch with
    | c :: _, _, hch =>
      obtain ⟨a, ha⟩ := (hch c (List.mem_cons_self)).exists_atom
      exact ⟨a, RecursiveComponent.mem_atoms_complex.mpr ⟨c, List.mem_cons_self, ha⟩⟩

/-- In a pairwise-related list of length ≥ 2, every element is related to some element
    (possibly itself, when the list repeats it). `#print axioms`: propext. -/
theorem List.exists_rel_of_pairwise {β : Type*} {R : β → β → Prop} {l : List β}
    (hp : l.Pairwise R) (hl : 2 ≤ l.length) {c : β} (hc : c ∈ l) :
    ∃ d ∈ l, R c d ∨ R d c := by
  match l, hp, hl, hc with
  | a :: b :: rest, hp, _, hc =>
    rw [List.pairwise_cons] at hp
    obtain ⟨hab, _⟩ := hp
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact ⟨b, by simp, Or.inl (hab b (by simp))⟩
    · exact ⟨a, by simp, Or.inr (hab c hc')⟩

/-- Two distinct atoms inside any complex node of a decomposition.
    `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem RecursiveComponent.IsDecomposition.exists_two_atoms {α : Type*} [ActsOn α]
    {a : α} {cs : List (RecursiveComponent α)}
    (hd : (RecursiveComponent.complex a cs).IsDecomposition) :
    ∃ x ∈ (RecursiveComponent.complex a cs).atoms,
      ∃ y ∈ (RecursiveComponent.complex a cs).atoms, x ≠ y := by
  cases hd with
  | complex _ _ hb hdisj _ hch =>
    match cs, hb, hdisj, hch with
    | c₁ :: c₂ :: _, _, hdisj, hch =>
      simp only [List.map_cons, List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at hdisj
      have h12 : Disjoint c₁.atomSet c₂.atomSet := hdisj.1.1
      obtain ⟨x, hx⟩ := (hch c₁ (by simp)).exists_atom
      obtain ⟨y, hy⟩ := (hch c₂ (by simp)).exists_atom
      refine ⟨x, RecursiveComponent.mem_atoms_complex.mpr ⟨c₁, by simp, hx⟩,
        y, RecursiveComponent.mem_atoms_complex.mpr ⟨c₂, by simp, hy⟩, ?_⟩
      rintro rfl
      exact Set.disjoint_left.mp h12 hx hy

/-- **The content of #2.** A hierarchical system has two modules `m₁ ≠ m₂` (top-level
    children's atom-sets), two distinct components `x, y` in `m₁`, and a component `z` in
    `m₂` outside `m₁`. This is what `nested` + `IsDecomposition` buy, and it is what every
    failure theorem below spends: it forces three components and a within/between split.
    `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem Hierarchical.exists_split {α : Type*} [ActsOn α] {σ : ConcreteSystem α}
    {T : Type*} [LinearOrder T] [InteractionStrength α T] (h : Hierarchical σ T) :
    ∃ m₁ ∈ h.nd.modules, ∃ m₂ ∈ h.nd.modules,
      ∃ x ∈ m₁, ∃ y ∈ m₁, x ≠ y ∧ ∃ z ∈ m₂, z ∉ m₁ := by
  obtain ⟨c, hc, hcomplex⟩ := h.nested
  have hdec := h.decomposition
  have hmod := h.modules_eq
  match ht : h.tree, c, hcomplex, hdec, hc with
  | .atomic _, _, _, _, hc =>
    simp [RecursiveComponent.children] at hc
  | .complex a cs, .atomic _, hcx, _, _ => exact hcx.elim
  | .complex a cs, .complex b ds, _, hdec, hc =>
    rw [ht] at hmod
    simp only [RecursiveComponent.children] at hc
    cases hdec with
    | complex _ _ hb hdisj _ hch =>
      -- a sibling module disjoint from the complex child's
      rw [List.pairwise_map] at hdisj
      obtain ⟨d, hd, hcd⟩ := List.exists_rel_of_pairwise hdisj hb hc
      have hdisj' : Disjoint (RecursiveComponent.complex b ds).atomSet d.atomSet := by
        rcases hcd with h | h
        · exact h
        · exact h.symm
      obtain ⟨x, hx, y, hy, hxy⟩ := (hch _ hc).exists_two_atoms
      obtain ⟨z, hz⟩ := (hch d hd).exists_atom
      refine ⟨(RecursiveComponent.complex b ds).atomSet, ?_, d.atomSet, ?_, x, hx, y, hy, hxy,
        z, hz, ?_⟩
      · rw [hmod]
        exact List.mem_map_of_mem hc
      · rw [hmod]
        exact List.mem_map_of_mem hd
      · exact fun hzc => Set.disjoint_left.mp hdisj' hzc hz

/-- The within/between asymmetry a hierarchical system exhibits somewhere: for the modules
    of `exists_split`, `strength x z < strength x y`.
    `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem Hierarchical.within_exceeds_between_somewhere {α : Type*} [ActsOn α]
    {σ : ConcreteSystem α} {T : Type*} [LinearOrder T] [InteractionStrength α T]
    (h : Hierarchical σ T) :
    ∃ m₁ ∈ h.nd.modules, ∃ m₂ ∈ h.nd.modules, m₁ ≠ m₂ ∧
      ∀ x ∈ m₁, ∀ y ∈ m₁, x ≠ y → ∀ z ∈ m₂,
        @strength α T _ x z < @strength α T _ x y := by
  obtain ⟨m₁, hm₁, m₂, hm₂, _, _, _, _, _, z, hz, hzm₁⟩ := h.exists_split
  have hne : m₁ ≠ m₂ := fun heq => hzm₁ (heq ▸ hz)
  exact ⟨m₁, hm₁, m₂, hm₂, hne, fun x hx y hy hxy z hz =>
    h.nd.within_exceeds_between hm₁ hm₂ hne hx hy hxy hz⟩

/-! ## Failure: uniform interaction admits no hierarchy -/

/-- The uniform interaction-strength profile: every pair interacts with strength `s`. -/
def uniformStrength (α : Type*) {T : Type*} (s : T) : InteractionStrength α T :=
  ⟨fun _ _ => s⟩

/-- **#2 can fail, substantively.** Under a uniform strength profile no concrete system on
    any carrier, under any action relation, is hierarchical: `exists_split` yields a
    within-module pair (strength ≥ threshold) and a between-module pair (strength <
    threshold) with the same strength. Simon's point exactly: with nothing to carve along,
    there are no modules. `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem not_hierarchical_of_uniform {α : Type*} [ActsOn α] (σ : ConcreteSystem α)
    {T : Type*} [LinearOrder T] (s : T) :
    @Hierarchical α _ σ T _ (uniformStrength α s) → False := by
  letI : InteractionStrength α T := uniformStrength α s
  intro h
  obtain ⟨m₁, hm₁, m₂, hm₂, x, hx, y, hy, hxy, z, hz, hzm₁⟩ := h.exists_split
  have hne : m₁ ≠ m₂ := fun heq => hzm₁ (heq ▸ hz)
  have hw := h.nd.within_strong m₁ hm₁ x hx y hy hxy
  have hb := h.nd.between_weak m₁ hm₁ m₂ hm₂ hne x hx z hz
  exact absurd (lt_of_lt_of_le hb hw) (lt_irrefl _)

/-- **#2 fails by cardinality on two things**, for every strength profile and every action
    relation: `exists_split` needs three pairwise distinct components.
    `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem not_hierarchical_bool {T : Type*} [LinearOrder T] (inst : ActsOn Bool)
    (str : InteractionStrength Bool T) (σ : @ConcreteSystem Bool inst) :
    @Hierarchical Bool inst σ T _ str → False := by
  letI := inst
  letI := str
  intro h
  obtain ⟨_, _, _, _, x, hx, y, hy, hxy, z, _, hzm₁⟩ := h.exists_split
  have hzx : z ≠ x := fun heq => hzm₁ (heq ▸ hx)
  have hzy : z ≠ y := fun heq => hzm₁ (heq ▸ hy)
  cases x <;> cases y <;> cases z <;> simp_all

/-! ## A two-level system that IS hierarchical

  Carrier `Fin 3`, components `0, 1, 2`, action `0 ▷ 1` and `1 ▷ 2` (a chain, so the system
  is connected and its modules interact). Tree: `{ {0, 1}, 2 }` — the subsystem `{0, 1}` and
  the atom `2`. Strength: `2` between `0` and `1`, `1` elsewhere; threshold `2`. -/

/-- The chain action on three things: `0 ▷ 1`, `1 ▷ 2`. -/
def chainActs : ActsOn (Fin 3) := ⟨fun x y => x.val + 1 = y.val⟩

/-- The graded strength profile: `0` and `1` interact at `2`, every other pair at `1`. -/
def gradedStrength : InteractionStrength (Fin 3) ℕ :=
  ⟨fun x y => if x.val + y.val = 1 then 2 else 1⟩

/-- The three-thing chain as a concrete system, everything in the composition. -/
def twoLevel : @ConcreteSystem (Fin 3) chainActs :=
  letI := chainActs
  { composition := Set.univ
    environment := ∅
    structure' := {p | p.1 ▷ p.2}
    disjoint := by simp
    structure_on := fun _ _ => by simp
    bondage_nonempty := ⟨0, trivial, 1, trivial, by decide, Or.inl rfl⟩ }

/-- The subsystem `{0, 1}` as a tree. -/
def subTree : RecursiveComponent (Fin 3) := .complex 0 [.atomic 0, .atomic 1]

/-- The decomposition tree `{ {0, 1}, 2 }`. The subsystem node's label `0` is arbitrary:
    the carrier has no element for the subsystem itself. -/
def twoLevelTree : RecursiveComponent (Fin 3) := .complex 0 [subTree, .atomic 2]

theorem mem_subTree_atomSet {x : Fin 3} : x ∈ subTree.atomSet ↔ x = 0 ∨ x = 1 := by
  simp [subTree, RecursiveComponent.atomSet, RecursiveComponent.atoms]

theorem mem_atomic_atomSet {α : Type*} {x a : α} :
    x ∈ (RecursiveComponent.atomic a).atomSet ↔ x = a := by
  simp [RecursiveComponent.atomSet, RecursiveComponent.atoms]

theorem twoLevelTree_modules :
    twoLevelTree.modules = [subTree.atomSet, (RecursiveComponent.atomic 2).atomSet] := rfl

/-- The subsystem `{0, 1}` is a decomposition (two bonded atoms). -/
theorem subTree_isDecomposition :
    @RecursiveComponent.IsDecomposition (Fin 3) chainActs subTree := by
  letI := chainActs
  refine .complex _ _ (by simp) ?_ ?_ ?_
  · refine List.pairwise_cons.mpr ⟨?_, List.pairwise_singleton _ _⟩
    intro m hm
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hm
    subst hm
    rw [Set.disjoint_left]
    intro a ha hb
    rw [mem_atomic_atomSet] at ha hb
    subst hb
    exact absurd ha (by decide)
  · exact ⟨0, by simp [RecursiveComponent.atomSet, RecursiveComponent.atoms],
      1, by simp [RecursiveComponent.atomSet, RecursiveComponent.atoms],
      by decide, Or.inl rfl⟩
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact .atomic _

/-- **#2 can hold.** The chain `0 ▷ 1 ▷ 2` under the graded profile is hierarchical with
    modules `{0, 1}` and `{2}`. `#print axioms`: propext, Classical.choice, Quot.sound. -/
def twoLevelHierarchical : @Hierarchical (Fin 3) chainActs twoLevel ℕ _ gradedStrength :=
  letI := chainActs
  letI := gradedStrength
  { tree := twoLevelTree
    atoms_eq := by
      ext a
      simp only [twoLevel, Set.mem_univ, iff_true]
      simp [twoLevelTree, subTree, RecursiveComponent.atomSet, RecursiveComponent.atoms]
      fin_cases a <;> decide
    nested := ⟨subTree, by simp [twoLevelTree, RecursiveComponent.children], trivial⟩
    decomposition := by
      refine .complex _ _ (by simp) ?_ ?_ ?_
      · refine List.pairwise_cons.mpr ⟨?_, List.pairwise_singleton _ _⟩
        intro m hm
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hm
        subst hm
        rw [Set.disjoint_left]
        intro a ha hb
        rw [mem_subTree_atomSet] at ha
        rw [mem_atomic_atomSet] at hb
        subst hb
        rcases ha with h | h <;> exact absurd h (by decide)
      · exact ⟨0, by simp [subTree, RecursiveComponent.atomSet, RecursiveComponent.atoms],
          1, by simp [subTree, RecursiveComponent.atomSet, RecursiveComponent.atoms],
          by decide, Or.inl rfl⟩
      · intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact subTree_isDecomposition
        · exact .atomic _
    nd :=
      { modules := twoLevelTree.modules
        threshold := 2
        covers := by
          intro c _
          rw [twoLevelTree_modules]
          simp only [List.mem_cons, List.not_mem_nil, or_false,
            exists_eq_or_imp, exists_eq_left, mem_subTree_atomSet, mem_atomic_atomSet]
          fin_cases c <;> decide
        within_strong := by
          intro m hm x hx y hy hxy
          rw [twoLevelTree_modules] at hm
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
          rcases hm with rfl | rfl
          · rw [mem_subTree_atomSet] at hx hy
            show (if x.val + y.val = 1 then 2 else 1) ≥ 2
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
              first | exact absurd rfl hxy | decide
          · rw [mem_atomic_atomSet] at hx hy
            subst hx; subst hy
            exact absurd rfl hxy
        between_weak := by
          intro m₁ hm₁ m₂ hm₂ hne x hx y hy
          rw [twoLevelTree_modules] at hm₁ hm₂
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hm₁ hm₂
          show (if x.val + y.val = 1 then 2 else 1) < 2
          rcases hm₁ with rfl | rfl <;> rcases hm₂ with rfl | rfl
          · exact absurd rfl hne
          · rw [mem_subTree_atomSet] at hx
            rw [mem_atomic_atomSet] at hy
            subst hy
            rcases hx with rfl | rfl <;> decide
          · rw [mem_atomic_atomSet] at hx
            rw [mem_subTree_atomSet] at hy
            subst hx
            rcases hy with rfl | rfl <;> decide
          · exact absurd rfl hne }
    modules_eq := rfl }

/-! ## The six cells among {#1 Systemness, #2 Hierarchical, #3 Networks} -/

/-- **#1 ⇏ #2** (`sep_systemness_hierarchical`). The chain `twoLevel` is a concrete system
    and, under the uniform profile, admits no hierarchy — the same system that is
    hierarchical under `gradedStrength` (`twoLevelHierarchical`). So #2's content over #1 is
    precisely the strength asymmetry; the bond graph does not decide it. The separation
    chooses the ambient strength (ᵃ), as `sep_hierarchy_systemness` chose the ambient action.
    `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem sep_systemness_hierarchical :
    (∃ _ : @ConcreteSystem (Fin 3) chainActs, True) ∧
      (∀ σ : @ConcreteSystem (Fin 3) chainActs,
        @Hierarchical (Fin 3) chainActs σ ℕ _ (uniformStrength (Fin 3) 1) → False) :=
  ⟨⟨twoLevel, trivial⟩, fun σ => @not_hierarchical_of_uniform (Fin 3) chainActs σ ℕ _ 1⟩

/-- **#1 ⇏ #2, choice-free** (`sep_systemness_hierarchical_bool`). A two-thing system under
    the lineage action, for every strength profile: a hierarchy needs three components in
    two modules (`exists_split`). Cardinality (ᶜ), the counterpart of the old
    `sep_hierarchy_systemness_unit`. `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem sep_systemness_hierarchical_bool :
    (∃ _ : @ConcreteSystem Bool lineageBool.toActsOn, True) ∧
      (∀ (T : Type) [LinearOrder T] (str : InteractionStrength Bool T)
        (σ : @ConcreteSystem Bool lineageBool.toActsOn),
        @Hierarchical Bool lineageBool.toActsOn σ T _ str → False) :=
  ⟨⟨lineageBool.toConcreteSystem ⟨false, true, ⟨rfl, rfl⟩, Bool.false_ne_true⟩,
      trivial⟩,
    fun _ _ str σ => not_hierarchical_bool lineageBool.toActsOn str σ⟩

/-- NOT SEPARABLE (#2 ⇒ #1): a hierarchy is a hierarchy OF a concrete system. This is
    Eq. 4.3 read literally — the complex component is `S_{i,j,l+1}`, a system — and it
    replaces both old witnesses (`sep_hierarchy_systemness`, `_unit`), which existed because
    `ImmediateAncestor` never asked for a bond. -/
def Hierarchical.toConcreteSystem {α : Type*} [ActsOn α] {σ : ConcreteSystem α}
    {T : Type*} [LinearOrder T] [InteractionStrength α T] (_ : Hierarchical σ T) :
    ConcreteSystem α := σ

/-- NOT SEPARABLE (#2 ⇒ #3): the bond graph of the decomposed system is a flow network with
    an edge, via #1's derivation. Replaces the old `sep_hierarchy_networks` (reflexive
    self-ancestry on `Unit`), which a decomposition cannot reproduce: `exists_split` needs
    three components. -/
def Hierarchical.toFlowNetwork {α κ : Type*} [ActsOn α] {σ : ConcreteSystem α}
    {T : Type*} [LinearOrder T] [InteractionStrength α T] (_ : Hierarchical σ T) (c : κ) :
    FlowNetwork α κ := σ.toFlowNetwork c

/-- The derived network has an edge. `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem Hierarchical.toFlowNetwork_edges_nonempty {α κ : Type*} [ActsOn α]
    {σ : ConcreteSystem α} {T : Type*} [LinearOrder T] [InteractionStrength α T]
    (h : Hierarchical σ T) (c : κ) : (h.toFlowNetwork c).edges.Nonempty :=
  σ.toFlowNetwork_edges_nonempty c

/-- The chain `0 → 1 → 2` as a flow network with unit capacity. -/
def chainNet : FlowNetwork (Fin 3) Unit where
  nodes := Set.univ
  edges := {⟨0, 1, ()⟩, ⟨1, 2, ()⟩}
  edges_on := fun _ _ => ⟨trivial, trivial⟩
  no_self_loops := fun e he => by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl <;> decide

/-- **#3 ⇏ #2** (`sep_networks_hierarchical`). A network with flow, under the uniform
    strength profile, is not hierarchical for ANY action relation and any system on the
    carrier: `not_hierarchical_of_uniform` never reads the bonds. Choice-free in the action
    (unlike `sep_networks_systemness`), chosen in the strength (ᵃ). Replaces the old
    derivation into a vacuous target. `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem sep_networks_hierarchical :
    chainNet.edges.Nonempty ∧
      (∀ (inst : ActsOn (Fin 3)) (σ : @ConcreteSystem (Fin 3) inst),
        @Hierarchical (Fin 3) inst σ ℕ _ (uniformStrength (Fin 3) 1) → False) :=
  ⟨⟨⟨0, 1, ()⟩, Or.inl rfl⟩,
    fun inst σ => @not_hierarchical_of_uniform (Fin 3) inst σ ℕ _ 1⟩

/- (#1,#3) and (#3,#1) do not mention #2 and are unchanged: `ConcreteSystem.toFlowNetwork`
   + `toFlowNetwork_edges_nonempty` (D), `sep_networks_systemness` (Wᵃ) with
   `FlowNetwork.toConcreteSystem` (D under the induced action), all in Matrix.lean. -/

end Systems
