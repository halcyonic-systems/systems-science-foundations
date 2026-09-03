/-
  Systems/Principles/Matrix.lean — the within-block independence matrix.

  Companion table: docs/paper/independence-matrix.md.

  THE FRAME. The eight axiom structures split by carrier:

    COMPONENT block {#1, #2, #3} — carrier is a component type `α` with a relation:
      #1 `ConcreteSystem α` (needs `[ActsOn α]`), #2 `ImmediateAncestor α`,
      #3 `FlowNetwork α κ`.
    STATE block {#4, #6, #8, #11, #12} — carrier is a state type `S` with a law `f : S → S`:
      #4 `DynamicSystem` (`law`), #6 `Evolution` (`step`), #8 `Homeostat` (`feedbackLaw`),
      #11 `Understanding` (`systemDyn`), #12 `Improvement`/`DirectedAgent` (`dyn`).

  "A ⇏ B" means: a concrete carrier carrying an A-instance, with a proof that no B-instance
  exists on it. Every ordered pair inside a block is attempted (6 + 20 = 26 cells). Cross-block
  pairs are out of scope: they need a component–state bridge that is a pending design decision.

  THE TIED CONVENTION (state block). Four of the five state structures are trivially
  instantiable on any carrier if the dynamics is free to vary (`Evolution` with `step := id`,
  `Homeostat` with `correct := fun _ s => s`, `DynamicSystem` with `law := id`,
  `Improvement` for any law with a moving state). So the block is read with ONE law per
  carrier and each structure asked to exist WITH ITS DYNAMICS EQUAL TO THAT LAW — the way
  the library's own witnesses are stated (`cyclic3_no_understanding` fixes `systemDyn`).
  The non-degeneracy conditions used, all defined below:
    #4  `Moving f`      some state moves
    #6  `EvolvesBy f`   f is the step of an Evolution for SOME fitness preorder, with a
                        strict climb somewhere
    #8  `Governs f`     f is the feedback law of a homeostat that is neutral at the set
                        point (the two hypotheses of `target_is_equilibrium`) and
                        effective (corrects some off-target state onto target)
    #11 `Understood f`  some `Understanding S M` has `systemDyn = f`
    #12 `Improved f`    some `Improvement S` has `dyn = f`;
        `Directed f`    some `DirectedAgent S M` has `understanding.systemDyn = f`
  Ambient instances that the target structure needs (a `Preorder` for #6, an `ActsOn` for
  #1) are quantified universally when they belong to the target and chosen when they belong
  to the source; where a separation only works by choosing a degenerate ambient instance,
  the docstring says so.

  Every theorem below has `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}; none
  uses `sorryAx`. The exact profile is recorded per theorem in its docstring (kernel output,
  2026-09-03).
-/
import Systems.Principles

namespace Systems

/-! ## Component block: {#1 Systemness, #2 Hierarchy, #3 Networks} -/

/-- The empty action relation: nothing acts on anything. Used where a separation is only
    available by choosing this degenerate ambient instance; the docstring of each such
    theorem flags it. -/
def noAction (α : Type*) : ActsOn α := ⟨fun _ _ => False⟩

/-- The action relation a flow network induces: `a` acts on `b` iff some edge runs `a → b`. -/
def FlowNetwork.toActsOn {α κ : Type*} (net : FlowNetwork α κ) : ActsOn α :=
  ⟨fun a b => (a, b) ∈ net.toRelation⟩

/-! ### #1 → #2 and #3 → #2: DERIVABLE, and the target is vacuous

  `ImmediateAncestor α` is a class with one field, a bare relation, and no law. It is
  inhabited on every carrier by `⟨fun _ _ => False⟩`, so "no #2-instance exists" is never
  true and no A ⇏ #2 cell can be witnessed. The canonical (data-carrying) realizations are
  recorded instead. -/

/-- Vacuous #2: every carrier has the empty ancestry. -/
def ImmediateAncestor.empty (α : Type*) : ImmediateAncestor α := ⟨fun _ _ => False⟩

/-- NOT SEPARABLE (#1 ⇒ #2): a concrete system's structure relation is an immediate-ancestry
    relation. (Vacuous target — see the section note.) -/
def ConcreteSystem.toImmediateAncestor {α : Type*} [ActsOn α] (σ : ConcreteSystem α) :
    ImmediateAncestor α :=
  ⟨fun x y => (x, y) ∈ σ.structure'⟩

/-- NOT SEPARABLE (#3 ⇒ #2): the relation a flow network induces is an immediate-ancestry
    relation. (Vacuous target — see the section note.) -/
def FlowNetwork.toImmediateAncestor {α κ : Type*} (net : FlowNetwork α κ) :
    ImmediateAncestor α :=
  ⟨fun x y => (x, y) ∈ net.toRelation⟩

/-! ### #1 → #3: DERIVABLE — the flow network is the bondage, with a capacity label -/

/-- NOT SEPARABLE (#1 ⇒ #3): the bond graph of a concrete system, restricted to its
    composition, is a flow network with constant capacity `c`. `no_self_loops` is the `a ≠ b`
    of `bondage_nonempty`; `edges_on` is membership in the composition. -/
def ConcreteSystem.toFlowNetwork {α κ : Type*} [ActsOn α] (σ : ConcreteSystem α) (c : κ) :
    FlowNetwork α κ where
  nodes := σ.composition
  edges := {e | e.source ∈ σ.composition ∧ e.target ∈ σ.composition ∧
    e.source ≠ e.target ∧ Bonded e.source e.target ∧ e.capacity = c}
  edges_on := fun _ he => ⟨he.1, he.2.1⟩
  no_self_loops := fun _ he => he.2.2.1

/-- The derived network is non-degenerate: it has an edge, supplied by `bondage_nonempty`.
    So #1 yields not just a `FlowNetwork` (the empty one always exists) but a network with
    flow. What #3 adds over #1 is exactly the capacity type `κ`. `#print axioms`: none. -/
theorem ConcreteSystem.toFlowNetwork_edges_nonempty {α κ : Type*} [ActsOn α]
    (σ : ConcreteSystem α) (c : κ) : (σ.toFlowNetwork c).edges.Nonempty := by
  obtain ⟨a, ha, b, hb, hne, hbond⟩ := σ.bondage_nonempty
  exact ⟨⟨a, b, c⟩, ha, hb, hne, hbond, rfl⟩

/-! ### #2 → #1: WITNESSED — ancestry without bonds -/

/-- A two-thing lineage: `false` is the immediate ancestor of `true`. -/
def lineageBool : ImmediateAncestor Bool := ⟨fun x y => x = false ∧ y = true⟩

/-- **#2 ⇏ #1** (`sep_hierarchy_systemness`). On `Bool` with the lineage `false ≺ true` and
    the empty action relation, there is ancestry between two distinct things but no concrete
    system: `bondage_nonempty` needs a bond and nothing acts on anything.

    Bunge's immediate ancestor is a historical relation (a precursor in the assembly of `y`),
    not a synchronic action, so a lineage among things that no longer act on one another is
    the intended reading, not a trick. But the separation does depend on choosing the ambient
    `ActsOn`; `sep_hierarchy_systemness_unit` gives the choice-free (cardinality) form.

    `#print axioms`: none. -/
theorem sep_hierarchy_systemness :
    (∃ x y : Bool, @ImmediateAncestor.immediateAncestor Bool lineageBool x y ∧ x ≠ y) ∧
      (@ConcreteSystem Bool (noAction Bool) → False) := by
  refine ⟨⟨false, true, ⟨rfl, rfl⟩, Bool.false_ne_true⟩, fun σ => ?_⟩
  letI := noAction Bool
  obtain ⟨_, -, _, -, -, hbond⟩ := σ.bondage_nonempty
  exact hbond.elim (fun h => h) (fun h => h)

/-- **#2 ⇏ #1, for every action relation.** A one-thing world is its own ancestor (the only
    nonempty relation on `Unit`) and is not a system under any `ActsOn`: a system needs two
    distinct components. This is the choice-free form; its cost is that the ancestry is
    reflexive, which an acyclicity requirement on #2 (proposed in the md) would rule out.

    `#print axioms`: none. -/
theorem sep_hierarchy_systemness_unit :
    (∃ x y : Unit, @ImmediateAncestor.immediateAncestor Unit ⟨fun _ _ => True⟩ x y) ∧
      (∀ (inst : ActsOn Unit), @ConcreteSystem Unit inst → False) := by
  refine ⟨⟨(), (), trivial⟩, fun _ σ => ?_⟩
  obtain ⟨a, _, b, _, hne, _⟩ := σ.bondage_nonempty
  exact hne (Subsingleton.elim a b)

/-- NOT SEPARABLE under the induced action (#2 ⇒ #1 when ancestry is read as action and has
    an off-diagonal pair): take `actsOn := immediateAncestor`; the composition is everything,
    the environment empty, the structure the ancestry itself. -/
def ImmediateAncestor.toActsOn {α : Type*} (inst : ImmediateAncestor α) : ActsOn α :=
  ⟨inst.immediateAncestor⟩

def ImmediateAncestor.toConcreteSystem {α : Type*} (inst : ImmediateAncestor α)
    (h : ∃ x y, inst.immediateAncestor x y ∧ x ≠ y) :
    @ConcreteSystem α inst.toActsOn := by
  letI := inst.toActsOn
  exact
    { composition := Set.univ
      environment := ∅
      structure' := {p | inst.immediateAncestor p.1 p.2}
      disjoint := by simp
      structure_on := fun _ _ => by simp
      bondage_nonempty := by
        obtain ⟨x, y, hxy, hne⟩ := h
        exact ⟨x, trivial, y, trivial, hne, Or.inl hxy⟩ }

/-! ### #2 → #3: WITNESSED (cardinality) — self-ancestry has no flow -/

/-- **#2 ⇏ #3** (`sep_hierarchy_networks`). A one-thing world with the reflexive ancestry
    admits no flow network with an edge, for any capacity type: `no_self_loops` needs two
    distinct nodes. The witness is a cardinality one and, like `sep_hierarchy_systemness_unit`,
    dies if #2 is required to be acyclic; under that requirement #2 ⇒ #3 by
    `ImmediateAncestor.toFlowNetwork`.

    `#print axioms`: propext, Quot.sound. -/
theorem sep_hierarchy_networks :
    (∃ x y : Unit, @ImmediateAncestor.immediateAncestor Unit ⟨fun _ _ => True⟩ x y) ∧
      (∀ (κ : Type) (net : FlowNetwork Unit κ), net.edges = ∅) := by
  refine ⟨⟨(), (), trivial⟩, fun κ net => Set.eq_empty_iff_forall_notMem.mpr fun e he => ?_⟩
  exact net.no_self_loops e he (Subsingleton.elim _ _)

/-- The derivation that survives acyclicity: an ancestry relation with an off-diagonal pair
    is a flow network on the whole carrier (edges = off-diagonal ancestry pairs, constant
    capacity `c`). -/
def ImmediateAncestor.toFlowNetwork {α κ : Type*} (inst : ImmediateAncestor α) (c : κ) :
    FlowNetwork α κ where
  nodes := Set.univ
  edges := {e | inst.immediateAncestor e.source e.target ∧ e.source ≠ e.target ∧
    e.capacity = c}
  edges_on := fun _ _ => ⟨trivial, trivial⟩
  no_self_loops := fun _ he => he.2.1

/-! ### #3 → #1: WITNESSED by ambient choice; DERIVABLE under the induced action -/

/-- A single flow `false → true` on `Bool`, unit capacity. -/
def oneFlow : FlowNetwork Bool Unit where
  nodes := Set.univ
  edges := {⟨false, true, ()⟩}
  edges_on := fun _ _ => ⟨trivial, trivial⟩
  no_self_loops := fun e he => by
    rw [Set.mem_singleton_iff] at he
    subst he
    exact Bool.false_ne_true

/-- **#3 ⇏ #1** (`sep_networks_systemness`). A network with a flow, under the empty action
    relation, is not a system. This separation exists only because `FlowNetwork` never
    mentions `ActsOn`: the two vocabularies are disconnected, and one can be filled while the
    other is left empty. Read with the action relation the network itself induces, the
    separation fails — see `FlowNetwork.toConcreteSystem`.

    `#print axioms`: propext. -/
theorem sep_networks_systemness :
    oneFlow.edges.Nonempty ∧ (@ConcreteSystem Bool (noAction Bool) → False) := by
  refine ⟨⟨⟨false, true, ()⟩, rfl⟩, fun σ => ?_⟩
  letI := noAction Bool
  obtain ⟨_, -, _, -, -, hbond⟩ := σ.bondage_nonempty
  exact hbond.elim (fun h => h) (fun h => h)

/-- NOT SEPARABLE under the induced action (#3 ⇒ #1): a flow network with at least one edge
    is a concrete system under the action relation it induces — composition = nodes,
    environment empty, structure = the underlying relation, and `no_self_loops` is exactly
    the `a ≠ b` that `bondage_nonempty` needs. A FINDING: the flow network's only content
    beyond CES is the capacity label; as a directed graph it and #1's bondage are the same
    datum read in two directions (`ConcreteSystem.toFlowNetwork` is the other). -/
def FlowNetwork.toConcreteSystem {α κ : Type*} (net : FlowNetwork α κ)
    (h : net.edges.Nonempty) : @ConcreteSystem α net.toActsOn := by
  letI := net.toActsOn
  exact
    { composition := net.nodes
      environment := ∅
      structure' := net.toRelation
      disjoint := by simp
      structure_on := fun p hp => by
        have := net.toRelation_on p hp
        simpa using this
      bondage_nonempty := by
        obtain ⟨e, he⟩ := h
        exact ⟨e.source, (net.edges_on e he).1, e.target, (net.edges_on e he).2,
          net.no_self_loops e he, Or.inl ⟨e, he, rfl⟩⟩ }

/-! ## State block: {#4 Dynamics, #6 Evolution, #8 Governance, #11 Understandability,
    #12 Improvability}

  One carrier `S`, one law `f : S → S`. The five tied predicates. -/

/-- #4, tied and non-degenerate: some state moves. (`DynamicSystem` itself is always
    inhabited for any law — `DynamicSystem.ofLaw` below — so this is the whole content.) -/
def Moving {S : Type*} (f : S → S) : Prop := ∃ s, f s ≠ s

/-- #6, tied and non-degenerate: `f` is the step of an `Evolution` for some fitness preorder
    on `S`, and climbs strictly somewhere. -/
def EvolvesBy {S : Type*} (f : S → S) : Prop :=
  ∃ (inst : Preorder S) (e : @Evolution S inst), @Evolution.step S inst e = f ∧
    ∃ s, @LT.lt S (@Preorder.toLT S inst) s (f s)

/-- #8, tied and non-degenerate: `f` is the feedback law of a homeostat that is neutral at
    its set point (the two hypotheses of `Homeostat.target_is_equilibrium`) and effective
    (some off-target state is corrected onto target in one tick). -/
def Governs {S : Type*} (f : S → S) : Prop :=
  ∃ (O : Type) (h : Homeostat S O), h.feedbackLaw = f ∧
    (∀ o, h.error o o = h.error h.setPoint h.setPoint) ∧
    (∀ s', h.correct (h.error h.setPoint h.setPoint) s' = s') ∧
    ∃ s, ¬ h.atTarget s ∧ h.atTarget (f s)

/-- #11, tied: some understanding has `f` as its system dynamics. (`Understanding` carries
    its own non-degeneracy: `compresses` and `nontrivial`.) -/
def Understood {S : Type*} (f : S → S) : Prop :=
  ∃ (M : Type) (u : Understanding S M), u.systemDyn = f

/-- #12 (bare), tied: some `Improvement` has `f` as its native dynamics. -/
def Improved {S : Type*} (f : S → S) : Prop := ∃ imp : Improvement S, imp.dyn = f

/-- #12 (full), tied: some `DirectedAgent` acts on a system whose dynamics is `f`. -/
def Directed {S : Type*} (f : S → S) : Prop :=
  ∃ (M : Type) (a : DirectedAgent S M), a.understanding.systemDyn = f

/-! ### Vacuity ledger — what each structure gives away for free -/

/-- Stock component side, so `DynamicSystem` can be instantiated inside the state block. -/
def allAction (α : Type*) : ActsOn α := ⟨fun _ _ => True⟩

def stockSystem : @ConcreteSystem Bool (allAction Bool) := by
  letI := allAction Bool
  exact
    { composition := Set.univ
      environment := ∅
      structure' := ∅
      disjoint := by simp
      structure_on := fun _ h => h.elim
      bondage_nonempty := ⟨false, trivial, true, trivial, Bool.false_ne_true, Or.inl trivial⟩ }

/-- VACUITY (#4): every law on every state type is the law of a `DynamicSystem`. -/
def DynamicSystem.ofLaw {S : Type*} (f : S → S) : @DynamicSystem Bool (allAction Bool) S := by
  letI := allAction Bool
  exact ⟨stockSystem, f⟩

/-- VACUITY (#6): the identity is an `Evolution` for every preorder (nothing gets less fit
    because nothing changes). -/
def Evolution.trivial (S : Type*) [Preorder S] : Evolution S := ⟨id, fun _ => le_refl _⟩

/-- VACUITY (#6, sharper): `Evolvable S` is a property of the fitness preorder alone. It holds
    iff the order has a strict pair, whatever the dynamics: the step "jump `s` to `t`, fix
    everything else" is an Evolution. So the `Evolvable (Fin 3)` half of
    `evolvable_but_not_improvable` is the statement `0 < 1` in `Fin 3`; `fin3climb` plays no
    role in it. `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem evolvable_iff_exists_lt (S : Type*) [Preorder S] : Evolvable S ↔ ∃ s t : S, s < t := by
  constructor
  · rintro ⟨e, s, hs⟩
    exact ⟨s, e.step s, hs⟩
  · rintro ⟨s, t, hst⟩
    classical
    refine ⟨⟨fun u => if u = s then t else u, fun u => ?_⟩, s, ?_⟩
    · by_cases hu : u = s
      · subst hu; simp [le_of_lt hst]
      · simp [hu]
    · simpa using hst

/-- VACUITY (#8): every law is the feedback law of a homeostat — sensor the identity, set point
    ignored, correction the law. The set point is data the feedback law need not read. The
    neutrality and effectiveness conditions in `Governs` are what make #8 non-degenerate. -/
def Homeostat.ofLaw {S : Type*} (s₀ : S) (f : S → S) : Homeostat S S :=
  ⟨s₀, id, fun o _ => o, fun o _ => f o⟩

theorem Homeostat.ofLaw_feedbackLaw {S : Type*} (s₀ : S) (f : S → S) :
    (Homeostat.ofLaw s₀ f).feedbackLaw = f := rfl

/-- VACUITY (#12, bare): a law admits an `Improvement` iff some state moves. The `intervene`
    field is unconstrained, so "drive straight to the goal" always works; `improves` and
    `genuine` then say only that the goal was not already at rest. Bare #12 coincides with
    non-degenerate #4. `#print axioms`: none. -/
theorem improved_iff_moving {S : Type*} (f : S → S) : Improved f ↔ Moving f := by
  constructor
  · rintro ⟨imp, rfl⟩
    exact ⟨imp.goal, imp.genuine⟩
  · rintro ⟨s, hs⟩
    exact ⟨⟨f, s, fun _ => Function.const S s, rfl, hs⟩, rfl⟩

/-! ### General lemmas the cells use -/

/-- Non-periodic point: `s` never returns to itself. -/
def Nonperiodic {S : Type*} (f : S → S) (s : S) : Prop := ∀ n, f^[n + 1] s ≠ s

/-- The reachability preorder of a law: `t ≤ u` iff `u` is reached from `t`. -/
def reachPreorder {S : Type*} (f : S → S) : Preorder S where
  le t u := ∃ n, f^[n] t = u
  le_refl _ := ⟨0, rfl⟩
  le_trans _ _ _ := fun ⟨m, hm⟩ ⟨n, hn⟩ => ⟨n + m, by rw [Function.iterate_add_apply, hm, hn]⟩

/-- A law is a non-degenerate blind evolution for some fitness order iff it has a
    non-periodic point. (⇒) A strict climb `s < f s` forbids returning, since every iterate is
    at least as fit. (⇐) Reachability is a fitness order under which `f` climbs.
    `#print axioms`: propext, Quot.sound. -/
theorem evolvesBy_iff_nonperiodic {S : Type*} (f : S → S) :
    EvolvesBy f ↔ ∃ s, Nonperiodic f s := by
  constructor
  · rintro ⟨inst, e, rfl, s, hs⟩
    refine ⟨s, fun n hn => ?_⟩
    have h1 : e.step s ≤ e.step^[n] (e.step s) := e.adapts n (e.step s)
    rw [← Function.iterate_succ_apply, hn] at h1
    exact (lt_iff_le_not_ge.mp hs).2 h1
  · rintro ⟨s, hs⟩
    letI := reachPreorder f
    refine ⟨reachPreorder f, ⟨f, fun t => ⟨1, rfl⟩⟩, rfl, s, ?_⟩
    refine ⟨⟨1, rfl⟩, fun ⟨n, hn⟩ => hs n ?_⟩
    rw [Function.iterate_succ_apply]
    exact hn

/-- A governing law has a fixed point reached in one tick from a non-fixed state.
    `#print axioms`: none. -/
theorem Governs.exists_fixed {S : Type*} {f : S → S} (h : Governs f) :
    ∃ s p, s ≠ p ∧ f s = p ∧ f p = p := by
  obtain ⟨O, h, hlaw, hz, hn, s, hs, hfs⟩ := h
  have hp : f (f s) = f s := by
    have := h.target_is_equilibrium (f s) hfs hz hn
    rwa [hlaw] at this
  exact ⟨s, f s, fun heq => hs (by rw [heq]; exact hfs), rfl, hp⟩

/-- Conversely, a law with a fixed point `p` reached in one tick from some `s ≠ p` governs:
    observe "am I at `p`", correct by `f` when not. `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem governs_of_fixed {S : Type*} {f : S → S} {s p : S} (hsp : s ≠ p) (hs : f s = p)
    (hp : f p = p) : Governs f := by
  classical
  refine ⟨Bool, ⟨true, fun t => decide (t = p), fun o o' => decide (o = o'),
    fun b t => if b then t else f t⟩, ?_, ?_, ?_, s, ?_, ?_⟩
  · funext t
    by_cases ht : t = p
    · subst ht; simp [Homeostat.feedbackLaw, hp]
    · simp [Homeostat.feedbackLaw, ht]
  · intro o; simp
  · intro t; simp
  · simp [Homeostat.atTarget, hsp]
  · simp [Homeostat.atTarget, hs]

/-- A point outside the range of `f`, plus two other distinct points, gives an understanding
    of `f` with the two-state model "am I at the unreachable point?" whose model dynamics is
    the constant `false`. This is a legitimate `Understanding` per the encoding and it
    predicts nothing that changes — the md proposes a non-degeneracy condition (non-constant
    `modelDyn`) that would exclude it. -/
noncomputable def Understanding.ofMissingPoint {S : Type*} (f : S → S) (c : S) (hc : ∀ s, f s ≠ c)
    (a b : S) (ha : a ≠ c) (hb : b ≠ c) (hab : a ≠ b) : Understanding S Bool :=
  { abstract := fun s => @decide (s = c) (Classical.propDecidable _)
    systemDyn := f
    modelDyn := fun _ => false
    abstracts := fun s => by simp [hc s]
    surjective := fun m => by
      cases m
      · exact ⟨a, by simp [ha]⟩
      · exact ⟨c, by simp⟩
    compresses := fun hinj => hab (hinj (by simp [ha, hb]))
    nontrivial := inferInstance }

/-- On a finite carrier with at least three states, every law that is not surjective is
    understood. `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem understood_of_not_surjective {S : Type*} [Fintype S] (f : S → S)
    (h3 : 2 < Fintype.card S) (hf : ¬ Function.Surjective f) : Understood f := by
  classical
  obtain ⟨c, hc⟩ : ∃ c, ∀ s, f s ≠ c := by
    by_contra hcon
    push_neg at hcon
    exact hf fun c => hcon c
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := Fintype.two_lt_card_iff.mp h3
  by_cases hx : x = c
  · subst hx
    exact ⟨Bool, Understanding.ofMissingPoint f x hc y z (Ne.symm hxy) (Ne.symm hxz) hyz, rfl⟩
  · by_cases hy : y = c
    · subst hy
      exact ⟨Bool, Understanding.ofMissingPoint f y hc x z hx (Ne.symm hyz) hxz, rfl⟩
    · exact ⟨Bool, Understanding.ofMissingPoint f c hc x y hx hy hxy, rfl⟩

/-- A bijection of a finite type has every point periodic. `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem exists_iterate_eq_self_of_bijective {S : Type*} [Fintype S] {f : S → S}
    (hf : Function.Bijective f) (s : S) : ∃ n, f^[n + 1] s = s := by
  classical
  let σ : Equiv.Perm S := Equiv.ofBijective f hf
  have hpos : 0 < orderOf σ := orderOf_pos σ
  refine ⟨orderOf σ - 1, ?_⟩
  have hk : (σ ^ orderOf σ) s = s := by rw [pow_orderOf_eq_one]; rfl
  rw [Equiv.Perm.coe_pow] at hk
  rw [Nat.sub_add_cancel hpos]
  exact hk

/-- On a finite carrier with at least three states, a non-degenerate blind evolution is
    understood: a strict climb means a non-periodic point, so `f` is not a bijection, so (finite)
    not surjective, so some state is never revisited, so the two-state "unreachable point"
    model is an understanding. **#6 ⇒ #11 on finite carriers with ≥ 3 states.**
    `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem understood_of_evolvesBy_finite {S : Type*} [Fintype S] (f : S → S)
    (h3 : 2 < Fintype.card S) (h : EvolvesBy f) : Understood f := by
  classical
  obtain ⟨s, hs⟩ := (evolvesBy_iff_nonperiodic f).mp h
  refine understood_of_not_surjective f h3 fun hsurj => ?_
  have hbij : Function.Bijective f := ⟨(Finite.injective_iff_surjective).mpr hsurj, hsurj⟩
  obtain ⟨n, hn⟩ := exists_iterate_eq_self_of_bijective hbij s
  exact hs n hn

/-- Understanding plus a moving state gives a directed agent: the agent's goal is a moving
    state and its intervention pins it. **#11 ∧ #4 ⇒ #12 (full).** -/
def DirectedAgent.ofUnderstanding {S M : Type*} (u : Understanding S M) (s : S)
    (hs : u.systemDyn s ≠ s) : DirectedAgent S M :=
  { understanding := u
    goal := s
    intervene := fun _ => Function.const S s
    improves := rfl
    genuine := hs }

theorem directed_of_understood_moving {S : Type*} {f : S → S} (hu : Understood f)
    (hm : Moving f) : Directed f := by
  obtain ⟨M, u, rfl⟩ := hu
  obtain ⟨s, hs⟩ := hm
  exact ⟨M, DirectedAgent.ofUnderstanding u s hs, rfl⟩

/-! ### Derivations (the NOT SEPARABLE cells) -/

/-- NOT SEPARABLE (#6 ⇒ #4): a strict climb moves. `#print axioms`: none. -/
theorem moving_of_evolvesBy {S : Type*} {f : S → S} (h : EvolvesBy f) : Moving f := by
  obtain ⟨_, _, rfl, s, hs⟩ := h
  exact ⟨s, fun heq => (lt_iff_le_not_ge.mp hs).2 (le_of_eq heq)⟩

/-- NOT SEPARABLE (#8 ⇒ #4): an effective correction moves. `#print axioms`: none. -/
theorem moving_of_governs {S : Type*} {f : S → S} (h : Governs f) : Moving f := by
  obtain ⟨s, p, hsp, hs, _⟩ := h.exists_fixed
  exact ⟨s, by rw [hs]; exact Ne.symm hsp⟩

/-- NOT SEPARABLE (#8 ⇒ #6): a governing law is a non-degenerate blind evolution — the
    corrected state `s` never returns (it sits at the fixed point `p ≠ s` forever), so
    reachability is a fitness order along which `f` climbs. Semantically: fitness = "reached
    the set point", selection = the feedback law. A FINDING: as encoded, governance is a
    special case of evolution rather than an alternative to it.
    `#print axioms`: propext, Quot.sound. -/
theorem evolvesBy_of_governs {S : Type*} {f : S → S} (h : Governs f) : EvolvesBy f := by
  obtain ⟨s, p, hsp, hs, hp⟩ := h.exists_fixed
  refine (evolvesBy_iff_nonperiodic f).mpr ⟨s, fun n hn => hsp ?_⟩
  rw [Function.iterate_succ_apply, hs, equilibrium_iterate hp n] at hn
  exact hn.symm

/-- NOT SEPARABLE (#12 ⇒ #4): a genuine improvement has a moving goal. `#print axioms`: none. -/
theorem moving_of_directed {S : Type*} {f : S → S} (h : Directed f) : Moving f := by
  obtain ⟨_, a, rfl⟩ := h
  exact ⟨a.goal, a.genuine⟩

/-- NOT SEPARABLE (#12 ⇒ #11): by construction, `DirectedAgent.toUnderstanding`.
    `#print axioms`: none. -/
theorem understood_of_directed {S : Type*} {f : S → S} (h : Directed f) : Understood f := by
  obtain ⟨M, a, ha⟩ := h
  exact ⟨M, a.understanding, ha⟩

/-- NOT SEPARABLE (#4 ⇒ #12 bare, #6 ⇒ #12 bare, #8 ⇒ #12 bare): anything that moves is
    improvable in the bare sense, by `improved_iff_moving`. `#print axioms`: none. -/
theorem improved_of_moving {S : Type*} {f : S → S} (h : Moving f) : Improved f :=
  (improved_iff_moving f).mpr h

/-- NOT SEPARABLE on finite carriers with ≥ 3 states (#6 ⇒ #12 full, #8 ⇒ #12 full): a
    non-degenerate blind evolution is understood and moves, hence admits a directed agent.
    The `Bool` witnesses below are therefore the only kind possible for #6 ⇏ #12 and
    #8 ⇏ #12 on finite carriers: the separation is by cardinality, not by dynamics.
    `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem directed_of_evolvesBy_finite {S : Type*} [Fintype S] (f : S → S)
    (h3 : 2 < Fintype.card S) (h : EvolvesBy f) : Directed f :=
  directed_of_understood_moving (understood_of_evolvesBy_finite f h3 h) (moving_of_evolvesBy h)

theorem directed_of_governs_finite {S : Type*} [Fintype S] (f : S → S)
    (h3 : 2 < Fintype.card S) (h : Governs f) : Directed f :=
  directed_of_evolvesBy_finite f h3 (evolvesBy_of_governs h)

/-! ### Witness carriers -/

/-- No two-state system is understood, for any dynamics: an onto map from `Bool` to a
    nontrivial type is injective. (`Understanding.card_lt` gives the general
    `card S ≤ 2` form; the direct proof avoids a `Fintype M`.) `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem no_understanding_of_bool {M : Type*} (u : Understanding Bool M) : False := by
  obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp u.compresses
  have hconst : ∀ x, u.abstract x = u.abstract a := by
    intro x
    cases a <;> cases b <;> cases x <;> first | rfl | exact hab.symm | exact hab | exact absurd rfl hne
  haveI := u.nontrivial
  obtain ⟨m₁, m₂, hm⟩ := exists_pair_ne M
  obtain ⟨x₁, rfl⟩ := u.surjective m₁
  obtain ⟨x₂, rfl⟩ := u.surjective m₂
  exact hm ((hconst x₁).trans (hconst x₂).symm)

theorem not_understood_bool (f : Bool → Bool) : ¬ Understood f :=
  fun ⟨_, u, _⟩ => no_understanding_of_bool u

theorem not_directed_bool (f : Bool → Bool) : ¬ Directed f :=
  fun h => not_understood_bool f (understood_of_directed h)

/-- A law with no fixed point does not govern. `#print axioms`: none. -/
theorem not_governs_of_no_fixed {S : Type*} {f : S → S} (h : ∀ s, f s ≠ s) : ¬ Governs f :=
  fun hg => by
    obtain ⟨_, p, _, _, hp⟩ := hg.exists_fixed
    exact h p hp

/-- A law all of whose points are periodic is not a blind evolution for any fitness order.
    `#print axioms`: propext, Quot.sound. -/
theorem not_evolvesBy_of_periodic {S : Type*} {f : S → S} (h : ∀ s, ∃ n, f^[n + 1] s = s) :
    ¬ EvolvesBy f := fun he => by
  obtain ⟨s, hs⟩ := (evolvesBy_iff_nonperiodic f).mp he
  obtain ⟨n, hn⟩ := h s
  exact hs n hn

/-! #### Carrier W1: the toggle `not : Bool → Bool` — moves, but nothing else -/

/-- **#4 ⇏ #6** (`sep_dynamics_evolution`). The toggle moves every state and is periodic at
    every state, so under no fitness order is it a non-degenerate evolution: blind selection
    cannot climb a cycle. `#print axioms`: propext, Quot.sound. -/
theorem sep_dynamics_evolution : Moving not ∧ ¬ EvolvesBy not :=
  ⟨⟨true, by decide⟩, not_evolvesBy_of_periodic fun s => ⟨1, by cases s <;> rfl⟩⟩

/-- **#4 ⇏ #8** (`sep_dynamics_governance`). The toggle has no fixed point, so no neutral
    effective homeostat has it as feedback law: a dynamics with no rest state has nothing to
    hold. (Contrast `Homeostat.ofLaw`: without neutrality any law, the toggle included, is a
    feedback law.) `#print axioms`: none. -/
theorem sep_dynamics_governance : Moving not ∧ ¬ Governs not :=
  ⟨⟨true, by decide⟩, not_governs_of_no_fixed fun s => by cases s <;> decide⟩

/-- **#4 ⇏ #11** (`sep_dynamics_understanding`). The toggle is not understood — two states
    cannot compress. The library's `cyclic3_modeling_not_understanding` is the sharper form
    (three states, obstruction from the dynamics). `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem sep_dynamics_understanding : Moving not ∧ ¬ Understood not :=
  ⟨⟨true, by decide⟩, not_understood_bool not⟩

/-- **#4 ⇏ #12 (full)** (`sep_dynamics_directed`). The toggle admits no directed agent (no
    understanding to carry); it does admit a bare `Improvement` (`boolImprovement`), so the
    bare form is NOT separated from #4 — see `improved_iff_moving`. `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem sep_dynamics_directed : Moving not ∧ ¬ Directed not ∧ Improved not :=
  ⟨⟨true, by decide⟩, not_directed_bool not, ⟨boolImprovement true, rfl⟩⟩

/-! #### Carrier W2: `Nat.succ` — climbs forever, never rests -/

/-- **#6 ⇏ #8** (`sep_evolution_governance`). Successor is a blind evolution (reachability is
    the usual order on ℕ, `0` never returns) with no fixed point, so it governs nothing: an
    unbounded climb has no set point. `#print axioms`: propext, Quot.sound. -/
theorem sep_evolution_governance : EvolvesBy Nat.succ ∧ ¬ Governs Nat.succ :=
  ⟨(evolvesBy_iff_nonperiodic _).mpr ⟨0, fun n => by simp [Function.iterate_succ_apply']⟩,
    not_governs_of_no_fixed fun n => Nat.succ_ne_self n⟩

/-! #### Carrier W3: the collapse `fun _ => true` on `Bool` under `false < true` -/

/-- The collapse governs: `true` is fixed and reached from `false`. `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem governs_collapse : Governs (fun _ : Bool => true) :=
  governs_of_fixed (s := false) (p := true) Bool.false_ne_true rfl rfl

theorem evolvesBy_collapse : EvolvesBy (fun _ : Bool => true) :=
  evolvesBy_of_governs governs_collapse

/-- **#6 ⇏ #11** (`sep_evolution_understanding`). The collapse to `true` is a blind evolution
    on two states, and two states are never understood. The separation is by cardinality and
    must be: `understood_of_evolvesBy_finite` shows that on any finite carrier with three or
    more states a blind evolution IS understood. `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem sep_evolution_understanding :
    EvolvesBy (fun _ : Bool => true) ∧ ¬ Understood (fun _ : Bool => true) :=
  ⟨evolvesBy_collapse, not_understood_bool _⟩

/-- **#6 ⇏ #12 (full)** (`sep_evolution_directed`). Same carrier: evolvable, not directed —
    by cardinality only (`directed_of_evolvesBy_finite`). Bare #12 holds. Note the library's
    `evolvable_but_not_improvable` is NOT a tied witness: its `Evolvable` half is the order on
    `Fin 3` (`evolvable_iff_exists_lt`) and its un-improvable half is a different law, the
    3-cycle. `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem sep_evolution_directed :
    EvolvesBy (fun _ : Bool => true) ∧ ¬ Directed (fun _ : Bool => true) ∧
      Improved (fun _ : Bool => true) :=
  ⟨evolvesBy_collapse, not_directed_bool _, improved_of_moving ⟨false, by decide⟩⟩

/-- **#8 ⇏ #11** (`sep_governance_understanding`). The collapse governs and is not
    understood — by cardinality only (`directed_of_governs_finite` covers ≥ 3 states).
    `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem sep_governance_understanding :
    Governs (fun _ : Bool => true) ∧ ¬ Understood (fun _ : Bool => true) :=
  ⟨governs_collapse, not_understood_bool _⟩

/-- **#8 ⇏ #12 (full)** (`sep_governance_directed`). Same carrier, same caveat. Bare #12
    holds, as `Homeostat.toImprovement` already showed in general.
    `#print axioms`: propext, Classical.choice, Quot.sound. -/
theorem sep_governance_directed :
    Governs (fun _ : Bool => true) ∧ ¬ Directed (fun _ : Bool => true) ∧
      Improved (fun _ : Bool => true) :=
  ⟨governs_collapse, not_directed_bool _, improved_of_moving ⟨false, by decide⟩⟩

/-! #### Carrier W4: the static `id` on `Fin 3` — understood, and nothing to do -/

/-- The static three-state system is understood: "is it state 0?" is a proper coarse-graining
    whose model dynamics is the identity. -/
def staticUnderstanding : Understanding (Fin 3) Bool where
  abstract := fun s => decide (s = 0)
  systemDyn := id
  modelDyn := id
  abstracts := fun _ => rfl
  surjective := fun m => by cases m <;> [exact ⟨1, by decide⟩; exact ⟨0, by decide⟩]
  compresses := fun hinj => absurd (hinj (show decide ((1 : Fin 3) = 0) = decide ((2 : Fin 3) = 0) by decide)) (by decide)
  nontrivial := inferInstance

/-- **#11 ⇏ #4** (`sep_understanding_dynamics`). The static system is understood and nothing
    moves: understanding does not require motion. `#print axioms`: propext. -/
theorem sep_understanding_dynamics : Understood (id : Fin 3 → Fin 3) ∧ ¬ Moving (id : Fin 3 → Fin 3) :=
  ⟨⟨Bool, staticUnderstanding, rfl⟩, fun ⟨_, hs⟩ => hs rfl⟩

/-- **#11 ⇏ #12 (bare and full)** (`sep_understanding_improvability`). The static system is
    understood and admits no improvement of either kind: every state is already at rest, so
    no goal is `genuine`. The already-perfect is un-improvable. `#print axioms`: propext. -/
theorem sep_understanding_improvability :
    Understood (id : Fin 3 → Fin 3) ∧ ¬ Improved (id : Fin 3 → Fin 3) ∧
      ¬ Directed (id : Fin 3 → Fin 3) :=
  ⟨⟨Bool, staticUnderstanding, rfl⟩,
    fun h => ((improved_iff_moving _).mp h).elim fun _ hs => hs rfl,
    fun h => (moving_of_directed h).elim fun _ hs => hs rfl⟩

/-! #### Carrier W5: the rotation `(· + 1)` on `Fin 4` — understood by parity, never rests -/

/-- The 4-cycle is understood: parity is a proper coarse-graining and the model dynamics is
    the toggle. Unlike the 3-cycle, 4 is composite, so an informative quotient exists. -/
def rotationUnderstanding : Understanding (Fin 4) Bool where
  abstract := fun s => decide (s.val % 2 = 0)
  systemDyn := fun s => s + 1
  modelDyn := not
  abstracts := by decide
  surjective := fun m => by cases m <;> [exact ⟨1, by decide⟩; exact ⟨0, by decide⟩]
  compresses := fun hinj => absurd (hinj (show decide ((0 : Fin 4).val % 2 = 0) = decide ((2 : Fin 4).val % 2 = 0) by decide)) (by decide)
  nontrivial := inferInstance

theorem rotation_periodic : ∀ s : Fin 4, ∃ n, (fun s : Fin 4 => s + 1)^[n + 1] s = s :=
  fun s => ⟨3, by revert s; decide⟩

theorem rotation_no_fixed : ∀ s : Fin 4, s + 1 ≠ s := by decide

/-- **#11 ⇏ #6** (`sep_understanding_evolution`). The 4-cycle is understood (parity) and is
    periodic everywhere, so it is a blind evolution under no fitness order.
    `#print axioms`: propext, Quot.sound. -/
theorem sep_understanding_evolution :
    Understood (fun s : Fin 4 => s + 1) ∧ ¬ EvolvesBy (fun s : Fin 4 => s + 1) :=
  ⟨⟨Bool, rotationUnderstanding, rfl⟩, not_evolvesBy_of_periodic rotation_periodic⟩

/-- **#11 ⇏ #8** (`sep_understanding_governance`). The 4-cycle is understood and has no fixed
    point, so it governs nothing. `#print axioms`: propext. -/
theorem sep_understanding_governance :
    Understood (fun s : Fin 4 => s + 1) ∧ ¬ Governs (fun s : Fin 4 => s + 1) :=
  ⟨⟨Bool, rotationUnderstanding, rfl⟩, not_governs_of_no_fixed rotation_no_fixed⟩

/-- The 4-cycle admits a directed agent: parity understanding, goal `0`, pin it. -/
def rotationAgent : DirectedAgent (Fin 4) Bool :=
  DirectedAgent.ofUnderstanding rotationUnderstanding 0 (by decide)

/-- **#12 ⇏ #6** (`sep_improvability_evolution`). The 4-cycle admits a directed agent and is a
    blind evolution under no fitness order. This is the direction the reading edition (§9)
    lists as having no witness; under the tied reading it has one. What can be deliberately
    improved need not be blindly evolvable: an agent can pin a state on a cycle that
    selection could never climb. `#print axioms`: propext, Quot.sound. -/
theorem sep_improvability_evolution :
    Directed (fun s : Fin 4 => s + 1) ∧ ¬ EvolvesBy (fun s : Fin 4 => s + 1) :=
  ⟨⟨Bool, rotationAgent, rfl⟩, not_evolvesBy_of_periodic rotation_periodic⟩

/-- **#12 ⇏ #8** (`sep_improvability_governance`). The 4-cycle admits a directed agent and
    governs nothing (no fixed point). Improvement rewrites the law; governance must work with
    it. `#print axioms`: propext. -/
theorem sep_improvability_governance :
    Directed (fun s : Fin 4 => s + 1) ∧ ¬ Governs (fun s : Fin 4 => s + 1) :=
  ⟨⟨Bool, rotationAgent, rfl⟩, not_governs_of_no_fixed rotation_no_fixed⟩

end Systems
