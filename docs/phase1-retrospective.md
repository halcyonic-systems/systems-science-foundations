# Phase 1 Retrospective: What Formalization Revealed About Bunge's Ontology

*A structured analysis of where the Lean 4 type-checker forced interpretation choices that Bunge's prose left ambiguous.*

**Project**: Systems Ontology — Lean 4 Formalization
**Scope**: Bunge, *Treatise on Basic Philosophy* Vol. 4, Ch. 1 (Definitions 1.1–1.19, Postulates 1.1–1.8, Theorems 1.1–1.3, Corollaries 1.1–1.2)
**Codebase**: 7 Lean modules, 845 lines, 74 declarations, zero `sorry`s
**Date**: 2026-02-17

---

## 1. Coverage Summary

Phase 1 formalizes the core of Bunge's Chapter 1 — the CES (Composition–Environment–Structure) triple and its immediate consequences. The table below maps every definition, postulate, theorem, and corollary in the chapter to its formalization status.

### Definitions

| # | Name | Status | File | Notes |
|---|------|--------|------|-------|
| 1.1 | Concrete system | **Formalized** | System.lean:34 | CES triple as `ConcreteSystem` structure |
| 1.2 | Model of a system (CES triple) | **Formalized** | System.lean:34 | Composition, environment, structure as `Set α` and `Set (α × α)` |
| 1.3 | Closed/open system | **Formalized** | System.lean:54–60 | `isClosed` and `isOpen` as predicates on environment emptiness |
| 1.4 | Open w.r.t. property P | **Partial** | System.lean:76 | `isOpenWrt` uses first-order predicate, losing Bunge's relational character (see §2e) |
| 1.5 | Internal/external structure | **Formalized** | System.lean:98–106 | Filter `structure'` by composition/environment membership |
| 1.6 | Subsystem relation | **Formalized** | System.lean:118–151 | Proved reflexive, transitive, antisymmetric (partial order) |
| 1.7 | Nested systems | **Formalized** | System.lean:167–170 | Chain of supersystems ordered by subsystem relation |
| 1.8 | Level structure | **Partial** | Level.lean:24–38 | Precedence captured; membership criterion (Def 1.8(ii)) omitted (see §4c) |
| 1.9 | Property system | **Omitted** | — | Requires unformalizable "state function" from Vol. 3 |
| 1.10 | Input | **Omitted** | — | Depends on Def 1.9; priority for Phase 2 (Mobus flows) |
| 1.11 | Output | **Omitted** | — | Depends on Def 1.9; priority for Phase 2 (Mobus flows) |
| 1.12 | Assembly | **Formalized** | Assembly.lean:26–36 | Includes self-assembly (line 43) and self-organization (line 50) |
| 1.13 | Qualitative novelty / emergence | **Partial** | Assembly.lean:69–85 | Snapshot-based, loses continuous interval semantics (see §3c) |
| 1.14 | Absolutely emergent | **Formalized** | Assembly.lean:112–114 | Set difference against universe-wide prior properties |
| 1.15 | Selective action | **Partial** | Selection.lean:31–37 | Set-based; selection pressure (Def 1.15(iii)) deferred (see §4d) |
| 1.16 | Ancestry / descent | **Partial** | Level.lean:104–135 | Transitive closure defined; irreflexivity unproved (see §4a) |
| 1.17 | Evolutionary lineage | **Omitted** | — | Requires domain-specific fitness and environmental change |
| 1.18 | Stability | **Omitted** | — | Requires dynamical systems notions (attractors, Lyapunov) |
| 1.19 | Cohesion | **Omitted** | — | Requires quantitative bond-strength comparison |

### Postulates

| # | Name | Status | File | Notes |
|---|------|--------|------|-------|
| 1.1 | Every system has at least two components | **Implicit** | System.lean:47 | Enforced by `bondage_nonempty` field (∃ a b, a ≠ b ∧ Bonded a b) |
| 1.2 | Every system is a component of some other system | **Omitted** | — | Existential claim about the universe of systems; requires external axiom |
| 1.3 | All components of a system interact (directly or via mediators) | **Omitted** | — | Would need graph-connectedness of bond relation |
| 1.4 | Every system was assembled from independent precursors | **Omitted** | — | Historical claim; related to Assembly but not identical |
| 1.5 | Assembly implies emergence and loss | **Stated** | Assembly.lean:127–132 | `PostulateAssemblyEmergence` as independent structure, not enforced on `Assembly` (see §3d) |
| 1.6 | Universal selection | **Stated** | Selection.lean:124–127 | `UniversalSelection` defined but not connected to system types |
| 1.7 | All systems have ancestry | **Omitted** | — | Existential claim about lineage; needs `ImmediateAncestor` instances |
| 1.8 | All systems are at some level | **Omitted** | — | Existential claim about level membership |

### Theorems and Corollaries

| # | Name | Status | File | Notes |
|---|------|--------|------|-------|
| Thm 1.1 | Subsystem relation is a partial order | **Formalized** | System.lean:126–151 | Reflexivity, transitivity, and antisymmetry proved separately |
| Thm 1.2 | Selection composition | **Formalized** | Selection.lean:75–115 | Core result: `compose_adapted_eq` is `rfl` (see §5a) |
| Thm 1.3 | Universal selection implies extinction cascade | **Omitted** | — | Requires population dynamics and temporal reasoning |
| Cor 1.1 | Universe is the only closed system | **Vacuously true** | System.lean:158–160 | Proved as `Iff.rfl` — reveals definitional redundancy (see §4b) |
| Cor 1.2 | Every system has at least one open property | **Omitted** | — | Follows from Cor 1.1 + Postulate 1.2; needs external axiom |

### Summary Statistics

- **Definitions**: 12/19 at least partially formalized (63%)
- **Postulates**: 3/8 at least stated (38%), 1/8 enforced by type (13%)
- **Theorems**: 2/3 fully proved (67%)
- **Corollaries**: 1/2 proved, though vacuously (50%)
- **Zero `sorry`s**: every stated claim is machine-checked

---

## 2. Where the Compiler Demanded Precision

These are cases where Lean's type-checker forced a concrete design decision on a point Bunge leaves informal or implicit. Each represents a genuine modeling choice with trade-offs — there is no single "correct" formalization.

### 2a. Time Parameterization Dropped

**Bunge's text**: Every definition is time-indexed — `C_A(σ,t)`, `E_A(σ,t)`, `S_A(σ,t)`. Def 1.2 explicitly states "the A-composition of σ *at a given time t*." The temporal qualifier appears in every definition through Chapter 1.

**What we did**: Each `ConcreteSystem` represents a *snapshot* at a fixed instant. There is no time parameter in the type.

```
-- System.lean:34
structure ConcreteSystem (α : Type*) [ActsOn α] where
  composition : Set α
  environment : Set α
  structure' : Set (α × α)
  ...
```

**Why**: Bunge never formalizes time beyond "instants in T ⊆ ℝ." His definitions all work at a fixed `t` — the time index is carried syntactically but never participates in the mathematical content until §2.2 (state functions and histories). A snapshot approach matches Bunge's actual usage: when he writes `C_A(σ,t)`, he means "the composition at time t," which is just a set.

**What this loses**: The formalization cannot express statements about temporal change *within a single type*. You cannot write "the composition at t' differs from the composition at t" as a property of one `ConcreteSystem`. You need two snapshots and an external assertion that they represent the same system at different times.

**Phase 2 relevance**: Mobus's `Δt` (the eighth tuple element) and the life-cycle formalization (`S_{t+1} = S_t ∪ ΔS`) require exactly this temporal threading. Phase 2 will need either an explicit time parameter or a `SystemHistory` type that sequences snapshots.

### 2b. Environment Is Declared, Not Derived

**Bunge's text** (Def 1.2(ii)):

> the A-environment of σ at time t is the set of all things of kind A, not components of σ, that act or are acted on by components of σ

In symbols: `E_A(σ,t) = {x ∈ A | x ∉ C_A ∧ ∃y ∈ C_A, x ▷ y ∨ y ▷ x}`.

The environment is a *derived set* — it is determined entirely by the composition and the action relation.

**What we did**: `environment : Set α` is a free field of `ConcreteSystem`, constrained only by disjointness with composition:

```
-- System.lean:37-42
environment : Set α
...
disjoint : composition ∩ environment = ∅
```

Nothing in the type forces environment members to actually interact with any component. You could construct a `ConcreteSystem` where `environment` contains things that have no bond with anything in `composition`.

**Why**: Making `environment` derived would require an additional field:

```
structure_coherent : ∀ x ∈ environment, ∃ y ∈ composition, x ▷ y ∨ y ▷ x
```

This is straightforward to state but complicates every construction of a `ConcreteSystem`: you'd need to provide evidence of interaction for every environment member. For Phase 1's goal of demonstrating that definitions compose, the simpler encoding was preferred.

**Significance**: This is a genuine gap between the formalization and Bunge's intention. The environment is supposed to be the maximal set of non-components that interact with the system — it's not a free parameter you choose. A `structure_coherent` field would close this gap and should be considered for Phase 2.

### 2c. `ActsOn` Lost Its State-Space Dependency

**Bunge's text** (§2.2, item x):

> A(x,y) = h(y|x) ∩ h̄(y) — the difference between the forced and free trajectory of the patient.

Action is defined in terms of *state-space trajectories*: thing `a` acts on thing `b` if and only if `b`'s trajectory through state space differs when `a` is present versus absent.

**What we did**: Bond.lean defines `HasStateSpace` (line 26) but `ActsOn` (line 36) does not reference it:

```
-- Bond.lean:26
class HasStateSpace (α : Type*) (S : outParam (Type*))

-- Bond.lean:36
class ActsOn (α : Type*) where
  actsOn : α → α → Prop
```

`ActsOn` is an opaque binary relation with no connection to state spaces. The docstring cites §2.2 but the type could represent any binary relation whatsoever — adjacency in a graph, alphabetical ordering, anything.

**Why**: The original plan called for state-parametric action (evidence that trajectories differ). The implementation simplified to an opaque relation because:
1. Bunge's trajectory definition requires a full state-space infrastructure (state functions, histories, lawful subspaces) that lives in State.lean and depends on System.lean — creating a circular dependency if Bond.lean needed it.
2. The `ActsOn` relation is used only to define `Bonded` and `Bondage`, where the specific evidence for action doesn't matter — only its existence.

**What this loses**: Nothing prevents someone from instantiating `ActsOn` with a relation that has nothing to do with causal influence. The formalization trusts the user to provide a meaningful instance. This is the trade-off between maximal generality (any relation works) and faithful encoding (only trajectory-modifying relations should count).

**Mitigation**: State.lean:96–99 defines `totalAction` as the set difference of forced and free histories, providing the trajectory-based definition of action *alongside* the opaque `ActsOn`. A Phase 2 theorem could connect these: "if `ActsOn` is consistent with `totalAction`, then..."

### 2d. `structure'` and `Bondage` Are Disconnected

**Bunge's text** (Def 1.2(iii)):

> the A-structure of σ at time t is the set of relations, in particular bonds, among the components of σ

Structure *includes* bondage as a subset: `B_A ⊆ S_A`. The bonds are part of the structure.

**What we did**: `ConcreteSystem` has an explicit `structure' : Set (α × α)` field (System.lean:40). `Bondage` is independently derived from `ActsOn` (Bond.lean:63). Nothing requires that bonded pairs appear in `structure'` or that `structure'` pairs be bonded:

```
-- System.lean:40
structure' : Set (α × α)

-- Bond.lean:63
def Bondage [ActsOn α] (X : Set α) : Set (α × α) :=
  {p | p.1 ∈ X ∧ p.2 ∈ X ∧ Bonded p.1 p.2}
```

The two sources of relational information are completely independent.

**Significance**: This disconnect has a downstream consequence for Assembly (see §3b). More broadly, it means the formalization has *two* notions of "the components are related" — one from the explicit structure field, one from the ActsOn typeclass — with no requirement that they agree. A `bondage_sub_structure` axiom (`Bondage composition ⊆ structure'`) would close this gap.

### 2e. "Property" Simplified to First-Order Predicate

**Bunge's text** (Def 1.4):

> σ is open w.r.t. P at t iff P is *related to* at least one *property of things* in E(σ,t)

This is a second-order concept: P is a property *of the system*, and the definition asks whether P is related to properties *of environmental things*. The "related to" is itself a relation between properties.

**What we did**:

```
-- System.lean:76-78
def ConcreteSystem.isOpenWrt [ActsOn α]
    (σ : ConcreteSystem α) (P : α → Prop) : Prop :=
  ∃ x ∈ σ.environment, P x
```

`P : α → Prop` is a predicate on *things*, not on properties. `isOpenWrt` asks whether any environmental thing satisfies the predicate — a first-order check.

**Why**: Encoding Bunge's second-order concept would require:
1. A type of properties (`Property : Type`)
2. A way to assign properties to systems and things
3. A relation between system-level and thing-level properties

This infrastructure would double the complexity of System.lean for a single definition. The first-order version still supports the key theorem (`closed_iff_closed_all`, System.lean:82–92), which is the main result Bunge draws from this definition.

**What this loses**: The distinction between "the system is open with respect to temperature" (P = has thermal exchange with environment) and "the system has a temperature-related property that depends on environmental temperatures" is collapsed. The second is Bunge's intended reading.

---

## 3. Interpretation Choices Between Plausible Readings

These are cases where Bunge's text is genuinely ambiguous or inconsistent, and the type-checker forced a resolution.

### 3a. "Reflexive, Asymmetric, and Transitive" (Def 1.6)

**Bunge's text**:

> [The subsystem relation] is an order relation, i.e. it is reflexive, asymmetric, and transitive.

**The problem**: A relation cannot be both reflexive and asymmetric. Reflexivity says `a ≤ a` for all `a`; asymmetry says `a ≤ b → ¬(b ≤ a)`. Applied to `a = b`: reflexivity gives `a ≤ a`, and asymmetry then gives `¬(a ≤ a)` — a contradiction.

Bunge clearly means *antisymmetric* (`a ≤ b ∧ b ≤ a → a = b`), i.e., the subsystem relation is a partial order.

**What we did**: System.lean proves reflexivity (line 126–128), transitivity (line 131–138), and antisymmetry (line 143–151) — the three properties of a partial order. The word "asymmetric" never appears.

```
-- System.lean:143-151
theorem subsystem_antisymm_components [ActsOn α]
    {σ₁ σ₂ : ConcreteSystem α}
    (h₁₂ : Subsystem σ₁ σ₂) (h₂₁ : Subsystem σ₂ σ₁) :
    σ₁.composition = σ₂.composition ∧
    σ₁.environment = σ₂.environment ∧
    σ₁.structure' = σ₂.structure' :=
  ⟨Set.Subset.antisymm h₁₂.1 h₂₁.1,
   Set.Subset.antisymm h₂₁.2.1 h₁₂.2.1,
   Set.Subset.antisymm h₁₂.2.2 h₂₁.2.2⟩
```

**Why this matters**: This is the cleanest example of formalization catching a textual error. A reader who takes "asymmetric" literally would conclude Bunge intended a strict partial order (irreflexive, asymmetric, transitive) — but then "every system is a subsystem of itself" (which Bunge asserts one paragraph later) would be false. The compiler makes this contradiction immediate. The resolution — antisymmetric, not asymmetric — is the only reading consistent with Bunge's surrounding text.

### 3b. Assembly Precursor Type Tension

**The setup**: An `Assembly` (Assembly.lean:26) contains a `precursor : ConcreteSystem α`. But `ConcreteSystem` requires `bondage_nonempty` (System.lean:47) — at least two different bonded components. The precursor is supposed to be an aggregate with *no* bonds.

**The tension**: `Assembly` also requires `precursor_unbonded : precursor.internalStructure = ∅` (Assembly.lean:34), asserting that the precursor's internal structure is empty. How can the precursor have nonempty bondage (required by the type) and empty internal structure (required by the assertion)?

**Why it works anyway**: `bondage_nonempty` uses `Bonded` (derived from `ActsOn`), while `internalStructure` (System.lean:98–100) filters `structure'` (the explicit field). Because `structure'` and `Bondage` are disconnected (§2d), you can have two things that are `Bonded` (via `ActsOn`) while `structure'` is empty. The type is satisfiable *only because of the gap from §2d*.

```
-- System.lean:47 — requires bonded things via ActsOn
bondage_nonempty : ∃ a ∈ composition, ∃ b ∈ composition, a ≠ b ∧ Bonded a b

-- System.lean:98-100 — filters explicit structure' field
def ConcreteSystem.internalStructure (σ : ConcreteSystem α) : Set (α × α) :=
  {p ∈ σ.structure' | p.1 ∈ σ.composition ∧ p.2 ∈ σ.composition}

-- Assembly.lean:34 — asserts empty internalStructure
precursor_unbonded : precursor.internalStructure = ∅
```

**The right fix**: Either:
- **(a)** Define a separate `Aggregate` type without the bondage constraint, and use it for the precursor. Bunge's aggregate is precisely a thing where composition is nonempty but bondage is empty — a different type.
- **(b)** Unify `structure'` and `Bondage` so the tension becomes a proper type error, forcing option (a).

The current state is satisfiable but accidental. It works because of an unintended gap, not because of a deliberate design choice.

### 3c. Emergence: Interval vs. Snapshot

**Bunge's text** (Def 1.13(i)):

> n_x(t,t') = p_x(t) △ ∪_{t<τ≤t'} p_x(τ)

The union runs over a *continuous time interval* (t, t']. It captures every property that appears at *any* moment during the interval — including transient properties that flash into existence and disappear.

**What we did**:

```
-- Assembly.lean:69-71
def qualitativeNovelty (before after : PropertySnapshot P) : Set P :=
  (before.properties \ after.properties) ∪ (after.properties \ before.properties)
```

We compare two `PropertySnapshot` values — "before" and "after" — losing everything that happens between them. The docstring (Assembly.lean:66–68) notes this simplification.

**What this loses**: A property that appears at τ₁ ∈ (t, t') and disappears before t' would be counted as emergent in Bunge's continuous-interval formulation but would be missed by our snapshot comparison. Our "emergence" is strictly weaker than Bunge's.

**Why**: Capturing the continuous interval would require either:
1. A measure-theoretic union indexed by a real-valued interval (heavy Mathlib dependencies)
2. A discrete sequence of snapshots with explicit temporal ordering

Neither fits Phase 1's goal of staying within basic set theory. The snapshot version preserves the key algebraic structure (emergence as set difference, novelty as symmetric difference) while deferring the temporal richness to Phase 2.

### 3d. Postulate 1.5 Unlinked to Assembly

**Bunge's text** (Postulate 1.5):

> Every assembly process is accompanied by the emergence of some properties and the loss of others.

This is a *universal* claim: for *every* assembly, both emergence and loss occur.

**What we did**: `PostulateAssemblyEmergence` and `Assembly` are defined as independent types:

```
-- Assembly.lean:26
structure Assembly (α : Type*) [ActsOn α] where ...

-- Assembly.lean:127
structure PostulateAssemblyEmergence {P : Type*}
    (before after : PropertySnapshot P) where
  gains : (emergentProperties before after).Nonempty
  losses : (lostProperties before after).Nonempty
```

Nothing connects them. You can construct an `Assembly` without a corresponding `PostulateAssemblyEmergence`. The postulate is *stated* but not *enforced*.

**Why**: Making the postulate a field of `Assembly` would require `Assembly` to carry a property type `P` and two `PropertySnapshot P` values. This would couple the structural concept (assembly = bondage from nothing) with the emergent concept (property gain/loss), making the type heavier and harder to instantiate. In Bunge's presentation, postulates are separate from definitions — they are global constraints on what kinds of systems can exist, not structural requirements on individual types.

**The trade-off**: The current design respects Bunge's separation between definitions and postulates at the cost of not enforcing the postulate via types. A user must *choose* to assert `PostulateAssemblyEmergence` when working with assembly. The compiler will not remind them.

---

## 4. Where Prose Turned Out Under-Specified

These are cases where the formalization attempt revealed that Bunge's definitions lack content, depend on unstated assumptions, or require infrastructure he never provides.

### 4a. Ancestry Irreflexivity Gap

**The claim** (Level.lean, header comment, line 9):

> SHOWCASE THEOREM #5: Ancestry is a strict partial order.

**What is actually proved**: Only transitivity.

```
-- Level.lean:133-135
theorem ancestor_trans [ImmediateAncestor α] {x y z : α}
    (hxz : Ancestor x z) (hzy : Ancestor z y) : Ancestor x y :=
  Ancestor.trans hxz hzy
```

**What is missing**: Irreflexivity — the statement that nothing is its own ancestor (`∀ x, ¬ Ancestor x x`). This would require an axiom about `ImmediateAncestor`:

```
-- Needed but absent:
axiom immediateAncestor_irrefl (x : α) : ¬ immediateAncestor x x
```

**Why it's missing**: `ImmediateAncestor` is a bare typeclass (Level.lean:104–106) with no constraints:

```
class ImmediateAncestor (α : Type*) where
  immediateAncestor : α → α → Prop
```

Nothing prevents an instance where `immediateAncestor x x` holds. Bunge's Def 1.16(i) says "x and y belong to the *same species*" as a condition, but "species" is an informal biological concept not encoded anywhere in the formalization.

**What this reveals**: Strict ordering of ancestry is not a consequence of the definitions — it depends on an external constraint (things cannot be their own precursors) that Bunge assumes tacitly. The formalization makes this assumption explicit by its absence.

### 4b. Corollary 1.1 Is Vacuously True

**Bunge's claim**: "The universe is the only closed system."

**What we proved**:

```
-- System.lean:158-160
theorem universe_only_closed (σ : ConcreteSystem α) :
    σ.isClosed ↔ σ.environment = ∅ :=
  Iff.rfl
```

This is `Iff.rfl` — reflexivity of bi-implication. The proof is *literally the definition*: `isClosed` *means* `environment = ∅`. There is no content.

**What the "corollary" actually claims**: Two things:
1. The universe has empty environment (which is the definition of "closed").
2. The universe is the *only* thing with empty environment.

Claim (2) is the substantive one. It depends on Bunge's Postulate 5.10 (from Volume 3, not Volume 4): *every concrete thing interacts with some other thing*. Without this axiom, there is no reason any system *must* have a non-empty environment.

**What this reveals**: The "corollary" has zero deductive content within Chapter 1 alone. It smuggles in an external axiom (universal interaction) and disguises it as a consequence of the definition. The Lean proof — `Iff.rfl` — makes this immediately visible.

### 4c. Level Membership Criterion Silently Dropped

**Bunge's text** (Def 1.8(ii)):

> a thing belongs to a given level iff it is composed of things in the preceding levels.

**What we formalized**:

```
-- Level.lean:32-38
structure LevelStructure (α : Type*) [Preorder α] where
  levels : List (Set α)
  levels_nonempty : ∀ L ∈ levels, Set.Nonempty L
  precedence : levels.Pairwise (fun Li Lj => LevelPrecedes Li Lj)
```

`LevelPrecedes Li Lj` (Level.lean:24) says: "for every thing in Lj, there exists a part in Li." But there is no converse constraint: a level could contain things whose parts are *not* in any lower level.

**What is missing**:

```
-- Needed but absent:
membership : ∀ L ∈ levels, ∀ x ∈ L,
  Composition x ⊆ ⋃₀ {L' | L' precedes L}
```

This would enforce that every thing at level j is *composed entirely* of things from lower levels — Bunge's compositional hierarchy. Without it, the `LevelStructure` is merely an ordered sequence of nonempty sets where higher levels contain things with *some* parts in lower levels, but possibly also parts from nowhere.

**What this reveals**: Bunge's level structure is more constrained than it appears. The compositional membership criterion makes levels a *partition* of the universe by compositional complexity, not just an ordering.

### 4d. Selection Pressure Requires Cardinality

**Bunge's text** (Def 1.15(iii)):

> The pressure of environment E on population S is: p_E = |S - A_E| / |S|

This is a *ratio of set sizes* — it requires counting.

**What we did**: Selection.lean uses `Set` throughout (infinite, no cardinality). The DESIGN comment (Selection.lean:15–16) explicitly notes this:

```
-- Selection.lean:15-16 (header)
-- DESIGN: We use Set-based definitions rather than Finset to keep imports
-- minimal and avoid decidability requirements.
```

Selection pressure is entirely deferred.

**What this reveals**: Bunge's definitions mix freely between pure set theory (arbitrary sets with membership) and measure theory (ratios of cardinalities) without noting the foundational shift. The `|S - A_E| / |S|` formula requires:
1. `S` to be finite (or have a well-defined measure)
2. Rational or real number arithmetic for the ratio
3. `S` to be nonempty (division by zero)

None of these are explicit in Bunge's text. The formalization forces the question: is selection defined for infinite populations? Bunge doesn't say.

---

## 5. Where Definitions Composed Cleanly

Not every encounter with the compiler was adversarial. Several of Bunge's definitions translated with surprising ease, and the proofs that result are illuminating precisely because they're *trivial*.

### 5a. Selection Composition Is Definitionally Equal

**Bunge's Theorem 1.2**: If environments E and E' act consecutively on a population, the composed selection is `i_{EE'} = i_{E'} ∘ i_E`.

**The proof**:

```
-- Selection.lean:100-104
theorem SelectiveAction.compose_adapted_eq
    (sel₁ : SelectiveAction α) (sel₂ : SelectiveAction α)
    (h : sel₂.population = sel₁.adapted) :
    (sel₁.compose sel₂ h).adapted = sel₂.adapted :=
  rfl
```

`rfl` — definitional equality. Not `simp`, not `ring`, not a multi-step chain. The composed selection's adapted set *is* the second selection's adapted set, by unfolding the definition.

**What this means**: Given the right type definitions, Bunge's theorem is not a theorem at all — it's a definitional consequence. The effort is entirely in choosing the right representation (`SelectiveAction.compose` at line 75–84), after which the result falls out for free. This is a strong signal that the definitions are "natural" in the mathematical sense.

### 5b. Emergence Decomposes Into Set Operations

**The theorem**: Qualitative novelty equals emergent ∪ lost.

```
-- Assembly.lean:89-93
theorem novelty_eq_emergent_union_lost
    (before after : PropertySnapshot P) :
    qualitativeNovelty before after =
      lostProperties before after ∪ emergentProperties before after := by
  simp [qualitativeNovelty, emergentProperties, lostProperties]
```

`simp` alone — the simplifier unfolds the definitions and recognizes that symmetric difference equals the union of two set differences. No manual work.

**What this means**: Bunge's philosophical point — that emergence is not mystical, it is precise set subtraction — is confirmed by the proof being automatic. The definitions are so clean that Lean's built-in simplifier sees through them. The `emergent_sub_novelty` theorem (line 96–101) similarly falls to `simp`.

### 5c. Subsystem Antisymmetry From Set Antisymmetry

**The theorem**: If σ₁ ≼ σ₂ and σ₂ ≼ σ₁, then their CES triples are componentwise equal.

```
-- System.lean:148-151
⟨Set.Subset.antisymm h₁₂.1 h₂₁.1,
 Set.Subset.antisymm h₂₁.2.1 h₁₂.2.1,
 Set.Subset.antisymm h₁₂.2.2 h₂₁.2.2⟩
```

Each component inherits antisymmetry from `Set.Subset.antisymm` in Mathlib. The three-component partial order "just works" by composing Mathlib's existing order theory — no custom lemmas needed.

**What this means**: Bunge's subsystem relation, despite being defined over triples with a mixed direction (composition ⊆, environment ⊇, structure ⊆), decomposes cleanly into three independent subset inclusions. The environment reversal (`σ₂.environment ⊆ σ₁.environment` in `Subsystem`, line 121) doesn't complicate antisymmetry because `Set.Subset.antisymm` works in both directions. The partial order structure is inherited, not constructed.

### 5d. Partition Theorem for Selection

**The theorem**: `adapted ∪ eliminated = population` and `adapted ∩ eliminated = ∅`.

```
-- Selection.lean:47-57
theorem SelectiveAction.partition (sel : SelectiveAction α) :
    sel.adapted ∪ sel.eliminated = sel.population := by
  ext x
  simp [SelectiveAction.eliminated, Set.mem_diff]
  ...

-- Selection.lean:60-66
theorem SelectiveAction.adapted_eliminated_disjoint (sel : SelectiveAction α) :
    sel.adapted ∩ sel.eliminated = ∅ := by
  ext x
  simp only [...]
  exact fun h _ => h
```

Both follow from `ext` + `simp` + minimal case analysis. The partition is a natural consequence of `eliminated` being defined as `population \ adapted`.

**What this means**: Bunge's set-theoretic definitions translate to Lean with almost no friction. The `ext` tactic (prove equality by showing membership coincides) is the workhorse — exactly as it should be for set-theoretic mathematics.

---

## 6. Omissions and Their Significance

The following definitions, postulates, theorems, and corollaries from Bunge Chapter 1 are *not* formalized. For each, a brief explanation of why and whether it matters for Phase 2.

### Definitions

| # | Name | Why Omitted | Phase 2 Priority |
|---|------|-------------|-----------------|
| 1.9 | Property system | Requires "state function" infrastructure from Vol. 3 §2.2; partially addressed by State.lean's `StateFunction` | Medium — needed for Mobus transforms |
| 1.10 | Input | Depends on Def 1.9 (property system) and boundary concept | **High** — central to Mobus's flow networks (G) |
| 1.11 | Output | Depends on Def 1.9; symmetric with Def 1.10 | **High** — central to Mobus's flow networks (G) |
| 1.17 | Evolutionary lineage | Requires fitness, environmental change, and temporal sequences beyond snapshot model | Low — domain-specific, not structural |
| 1.18 | Stability | Requires attractors, Lyapunov-style reasoning, dynamical systems | Medium — relevant for Mobus governance (H) |
| 1.19 | Cohesion | Requires quantitative comparison of internal vs. external bond strengths | Low — needs numerical infrastructure |

### Postulates

| # | Name | Why Omitted | Significance |
|---|------|-------------|-------------|
| 1.1 | ≥2 components | *Implicitly enforced* by `bondage_nonempty` (requires two distinct bonded things) | Already captured, just not as a named axiom |
| 1.2 | Every system is part of another | Existential claim about the universe of systems; cannot be enforced locally | Would require a global `SystemUniverse` axiom |
| 1.3 | All components connected | Requires graph-connectedness of bond relation over composition | Moderate — could be added as a field |
| 1.4 | Historical assembly | Claims every system was *once* assembled; temporal/historical, not structural | Low — Phase 2 life-cycle may address |
| 1.7 | Universal ancestry | Claims all systems have ancestors; existential | Low — domain-specific |
| 1.8 | Universal level membership | Claims all systems belong to some level; existential | Low — needs level-universe infrastructure |

### Theorems and Corollaries

| # | Name | Why Omitted | Significance |
|---|------|-------------|-------------|
| Thm 1.1 | Subsystem is partial order | *Proved* as three separate theorems (refl, trans, antisymm); not bundled as a `PartialOrder` instance | Could be upgraded to a Mathlib `PartialOrder` instance in Phase 2 |
| Thm 1.3 | Universal selection → extinction cascade | Requires temporal population dynamics and iterated selection | Low for Phase 2 (specialized) |
| Cor 1.2 | Every system has ≥1 open property | Requires Cor 1.1 + Postulate 1.2; circular without external axiom | Low — content depends on Vol. 3 axiom |

### Key Insight: Input/Output Definitions Are Phase 2 Priorities

Definitions 1.10 and 1.11 (input and output) define how matter, energy, and information cross a system's boundary. These are exactly the concepts that Mobus's flow networks (the N and G components of the 8-tuple) formalize computationally. Any Phase 2 `MobusSystem` that includes flow networks will need these definitions as a bridge from Bunge's general framework to Mobus's concrete one.

---

## Appendix: Codebase Statistics

| File | Lines | Definitions | Theorems | Structures |
|------|-------|-------------|----------|------------|
| Thing.lean | 54 | 2 | 3 | 0 |
| Bond.lean | 79 | 3 | 2 | 0 |
| System.lean | 172 | 7 | 4 | 1 |
| Level.lean | 137 | 7 | 2 | 2 |
| Assembly.lean | 134 | 5 | 2 | 4 |
| Selection.lean | 128 | 3 | 4 | 1 |
| State.lean | 141 | 7 | 2 | 2 |
| **Total** | **845** | **34** | **19** | **10** |

Additional: 11 classes/inductives, bringing total declarations to 74.

**Lean toolchain**: v4.28.0 (Mathlib-pinned)
**Dependencies**: Mathlib (Order.Defs.PartialOrder, Data.Set.Basic)
**Zero `sorry`s**: every claim is machine-verified
