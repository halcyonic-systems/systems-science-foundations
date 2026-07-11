# Categorification Roadmap: Three Phases

## Overview

This roadmap translates the existing Lean formalization of Bunge/Mobus/Klir systems theory and the BRA cryptocurrency models into categorical language. Each phase is independently publishable. The workflow throughout is: **sketch → prototype in CatLab.jl → certify in Lean/Mathlib**.

### Design Principle: Don't Categorify for Its Own Sake

Each categorical upgrade must answer a question that the current formalization can't. If wrapping something in `CategoryTheory.Functor` just restates what we already proved, it's not worth the infrastructure cost. The test: **does the categorical language make a new theorem statable or an existing theorem shorter?**

---

## Phase 1: Package Existing Results as Categories

**Timeline:** Now → ISSS/AITP submissions (May–August 2026)  
**Effort:** ~2 weeks CatLab.jl exploration + ~2 weeks Lean formalization  
**Publishable as:** Section in ISSS talk, remarks in journal paper  
**Risk:** Low — this is relabeling, not discovering  

### 1.1 Subsystem Ordering as a Thin Category

**What we have:** A partial order on `ConcreteSystem α` defined by composition inclusion, environment inclusion, and structure restriction.

**Categorical translation:** A preorder is a thin category (at most one morphism between any two objects). Define:

```
instance : Category (ConcreteSystem α) where
  Hom σ₁ σ₂ := σ₁ ≤ σ₂  -- subsystem relation as morphism type
  id := le_refl
  comp := le_trans
```

**What this buys us:** Subsystem relationships become composable. "σ₁ is a subsystem of σ₂ which is a subsystem of σ₃" isn't just a chain of inequalities — it's a commuting diagram. More importantly, it sets up the language for Phase 1.3.

**CatLab.jl exploration:**
- Define the category of Bunge systems as a finite category on test examples
- Compute whether specific inclusions compose as expected
- Visualize the Hasse diagram as a category

**Lean formalization:**
- `Mathlib.Order.Category.Preord` provides the infrastructure
- Main work: showing the subsystem relation is actually a preorder (reflexive, transitive) — likely already proved or trivial from existing definitions

### 1.2 Flattening as a Functor, Finding 3 as Naturality

**What we have:** `StructureFamily` (rich representation) and flat `Structure` (simplified representation), connected by `flatten := ⋃₀`. Finding 3: flattening commutes with internal/external decomposition.

**Categorical translation:** Define two categories:
- **RichSys**: Objects are systems with structure families. Morphisms are subsystem embeddings that respect the family decomposition.
- **FlatSys**: Objects are systems with flat structure. Morphisms are subsystem embeddings.

The flattening operation is a functor `Flatten : RichSys ⥤ FlatSys`.

Finding 3 says: the square

```
         internal_family
RichSys ─────────────────→ RichSys
   |                           |
   | Flatten                   | Flatten
   ↓                           ↓
FlatSys ─────────────────→ FlatSys
          internal_flat
```

commutes. This is a **natural transformation** between two composite functors. Or more precisely: `internal` is a natural endomorphism on the identity functor, and `Flatten` preserves it.

**What this buys us:** The naturality framing is *stronger* than the bare commutation theorem. It says the commutation holds not just for individual systems but coherently across all morphisms between systems. If someone later defines a new kind of system morphism, naturality guarantees the commutation still holds — it's structural, not accidental.

**CatLab.jl exploration:**
- Define both categories on small examples (3-4 systems)
- Define the functor and check it preserves composition
- Compute the naturality square on test instances
- Visualize the functor as a diagram

**Lean formalization:**
- Define `RichSys` and `FlatSys` as `CategoryTheory.Category` instances
- Define `Flatten` as `CategoryTheory.Functor`
- State Finding 3 as `CategoryTheory.NatTrans` or as commutativity of a functor square
- Key Mathlib imports: `Mathlib.CategoryTheory.Functor.Basic`, `Mathlib.CategoryTheory.NatTrans`

### 1.3 The Three Subsystem Orderings as a Functor Triangle (Finding 8)

**What we have:** Three distinct subsystem orderings from the StructureFamily exploration — pointwise, refinement, hybrid — forming a strict hierarchy.

**Categorical translation:** Three thin categories on the same objects (systems), related by **forgetful functors**:

```
     Refinement
         |
         | forget (coarser)
         ↓
      Hybrid
         |
         | forget (coarser)
         ↓
     Pointwise
```

Each forgetful functor is faithful (injective on morphisms — since all categories are thin, this means: if σ₁ ≤_refinement σ₂, then σ₁ ≤_hybrid σ₂, etc.). The strict hierarchy = the functors are faithful but NOT full (there exist hybrid-subsystem pairs that aren't refinement-subsystem pairs).

**What this buys us:** "The choice of structure representation determines which subsystem ordering you get" becomes precise: it's the choice of which forgetful functor to apply. Different audiences (Bunge readers vs. Mobus readers vs. Klir readers) are implicitly working in different categories related by these functors.

**CatLab.jl exploration:**
- Define all three orderings on a small example set
- Verify the forgetful functors exist and are faithful
- Find a witness for non-fullness (a morphism in the image that has no preimage)
- Generate a diagram showing the three categories and functors

**Lean formalization:**
- Three `Category` instances on the same type
- Three `Functor` definitions (forgetful)
- Proofs: `Faithful` (from Mathlib) for each functor
- Proofs: `¬ Full` for each functor (witness-based, like `collapse_not_injective`)

### 1.4 Mobus-Bunge Bridge as a Functor (Finding 6)

**What we have:** `Bridge.lean` connects Mobus 8-tuples to Bunge ⟨C,E,S⟩ triples. `totalRelation = N.toRelation ∪ G.toRelation`. `toRichBunge_flatten_eq` shows this is the flattening of the natural two-element structure family {N, G}.

**Categorical translation:** Define:
- **MobusSys**: Category of Mobus-style systems with morphisms being structure-preserving maps that respect the N/G decomposition
- **BungeSys**: Category of Bunge-style systems (= FlatSys from 1.2)

The bridge is a functor `Bridge : MobusSys ⥤ BungeSys` that factors through `RichSys`:

```
MobusSys ──embed──→ RichSys ──Flatten──→ BungeSys
    \                                    ↗
     \_________ Bridge ________________/
```

**What this buys us:** The factorization `Bridge = Flatten ∘ Embed` is the categorical content of Finding 6. It says the Mobus-to-Bunge passage is *exactly* the composition of (a) viewing Mobus's N/G as a structure family, then (b) flattening. This factorization is a **theorem about the relationship between frameworks** that neither Bunge nor Mobus stated.

**CatLab.jl exploration:**
- Define MobusSys on test examples
- Verify the factorization computationally
- Visualize the functor triangle

**Lean formalization:**
- `MobusSys` as `Category` instance
- `Embed : MobusSys ⥤ RichSys` and show `Bridge = Flatten ⋙ Embed`
- This is the categorical punchline of the StructureFamily exploration

### Phase 1 Deliverables

| Deliverable | Venue | Content |
|---|---|---|
| Subsystem thin category | Journal remark | §1.1 |
| Flattening functor + naturality | Journal section | §1.2, core result |
| Three orderings as functor triangle | Journal section | §1.3, from Finding 8 |
| Bridge factorization | ISSS talk centerpiece | §1.4, from Finding 6 |
| CatLab.jl visualizations | ISSS slides | All subsections |

---

## Phase 2: Categorify the BRA/Collapse Infrastructure — ✅ COMPLETE (2026-02-18)

**Completed:** 2026-02-18. 198 lines across 4 new files in `bitcoin-bra/`, zero sorry's.
**Publishable as:** Closes the noted limitation in BRA paper — collapse is now a proper Mathlib functor
**Actual effort:** ~1 session (same day as Phase 1), no CatLab.jl needed
**Actual risk:** Low — thin Eth category (same pattern as Phase 1) eliminated composition-proof risk

### 2.1 Btc and Eth as Proper Categories — ✅ Done

**Files:** `Bitcoin/Category.lean` (55 lines), `Comparison/EthCategory.lean` (25 lines)

**Actual implementation** (differs from original plan — simpler):

```lean
-- Btc: non-thin, list-based morphisms (essential for ¬ Faithful)
structure BtcState where utxos : UTXOSet
instance : Category BtcState where
  Hom s₁ s₂ := { txs : List Transaction // ValidBtcTrace s₁.utxos txs s₂.utxos }
  id _ := ⟨[], .nil⟩
  comp f g := ⟨f.1 ++ g.1, appendTrace f.2 g.2⟩
  -- Laws reduce to List.nil_append, List.append_nil, List.append_assoc via Subtype.ext

-- Eth: thin preorder category via totalValue ordering (same pattern as Phase 1!)
structure EthState where balances : BalanceMap
instance : Preorder EthState where
  le e₁ e₂ := e₂.balances.totalValue ≤ e₁.balances.totalValue
  -- Mathlib's Preorder.smallCategory gives Category instance for free
  comp := sequentialTransfer
```

**Key design decision:** Thin Eth (totalValue ordering) sidesteps the transfer-composition question entirely. The original plan's Eth with full transfer morphisms was the high-risk path. The thin approach — same pattern used in Phase 1 for subsystem orderings — gives a proper category with zero composition-proof overhead. Non-thin Btc (list-based morphisms) is essential for `¬ Faithful` — you need two *different* morphisms between the same endpoints.

**What was NOT needed:** CatLab.jl exploration, AlgebraicPetri.jl. The thin Eth pattern was proven in Phase 1.

### 2.2 Collapse as a Proper Functor — ✅ Done

**File:** `Comparison/CollapseFunctor.lean` (75 lines)

**Actual implementation:**

```lean
noncomputable def collapseFunctor : BtcState ⥤ EthState where
  obj := collapseObj                         -- wraps collapse
  map f := homOfLE (collapse_trace_le f.2)   -- valid trace → Eth ordering
  map_id _ := Subsingleton.elim _ _          -- thin target: trivial
  map_comp _ _ := Subsingleton.elim _ _      -- thin target: trivial
```

**NEW theorems proved:**

- **`EssSurj collapseFunctor`** ✅: Essentially surjective. Uses `collapse_surjective` + `eqToIso`.
- **`collapse_not_faithful_cat`** ✅: `¬ collapseFunctor.Faithful`. Concrete witness: two single-transaction traces ([consume/reproduce u3] and [consume/reproduce u7]) are distinct BtcState endomorphisms that map to the same unique EthState morphism. This WAS the justification for Phase 2 — a genuinely new result that the pre-categorical formalization literally could not state.
- **Full at path level** (observation): With thin Eth, collapse is actually `Full` at the category level. Non-fullness manifests only at the quiver level (single transactions). This is itself a publishable observation.
- **`¬ Monoidal`**: Deferred — requires `MonoidalCategory BtcState` (~12 coherence axioms).

### 2.3 Conservation as Functor Property — ✅ Done

**File:** `Comparison/Conservation.lean` (43 lines)

**Actual implementation:**

```lean
-- Object level: totalValue ∘ collapse = totalValue
theorem conservation_functor_obj (s : BtcState) :
    (collapseFunctor.obj s).balances.totalValue = s.utxos.totalValue :=
  conservation_commutes s.utxos

-- Morphism level (zero-fee case): exact conservation
theorem zero_fee_conservation {s₁ s₂ : BtcState} {txs : List Transaction}
    (h : ValidBtcTrace s₁.utxos txs s₂.utxos)
    (hfee : ∀ tx ∈ txs, tx.fee = 0) :
    s₂.utxos.totalValue = s₁.utxos.totalValue
```

**What was achieved:** Conservation restated using the functor's categorical vocabulary. `conservation_functor_obj` says "collapse preserves total value" at the functor-object level. `zero_fee_conservation` adds the morphism-level result: zero-fee transaction traces preserve value exactly.

**What was NOT needed:** Full `totalValueBtc`/`totalValueEth` functors to ℕ-Monoid. The direct restatement using `collapseFunctor.obj` is cleaner and avoids building unnecessary infrastructure.

### 2.4 Monoidal Structure for Btc (Connecting to Nester) — Deferred

**Status:** Not attempted. Deferred as stretch goal — the core Phase 2 value (functor + EssSurj + ¬Faithful + conservation) doesn't require monoidal structure.

**Why deferred:** `MonoidalCategory` has ~12 fields and 10 coherence axioms. The morphism-level tensor (parallel transactions on disjoint UTXO sets) requires careful handling of the `whiskerLeft`/`whiskerRight` operations. High effort-to-value ratio given the core results are already proved.

**If revisited:** The natural approach is `tensorObj s₁ s₂ := ⟨s₁.utxos + s₂.utxos⟩` (multiset union) with `tensorUnit := ⟨∅⟩`. Most coherence axioms should follow from `Multiset` being a commutative monoid under `+`. CatLab.jl exploration could help validate the structure before attempting the full Lean formalization.

### Phase 2 Deliverables — Actual

| Deliverable | Status | Content |
|---|---|---|
| `BtcState` non-thin category (list morphisms) | ✅ Done | Bitcoin/Category.lean, 55 lines |
| `EthState` thin preorder category (totalValue) | ✅ Done | Comparison/EthCategory.lean, 25 lines |
| `collapseFunctor : BtcState ⥤ EthState` | ✅ Done | Comparison/CollapseFunctor.lean |
| `EssSurj collapseFunctor` | ✅ Done | Uses `collapse_surjective` + `eqToIso` |
| `collapse_not_faithful_cat` | ✅ Done | **New result** — not statable without categories |
| `conservation_functor_obj` | ✅ Done | Comparison/Conservation.lean |
| `zero_fee_conservation` | ✅ Done | Comparison/Conservation.lean |
| `MonoidalCategory BtcState` | Deferred | Stretch goal, §2.4 |

**Total:** 198 lines, 4 files, 15 new declarations, zero `sorry`s.

---

## Phase 3: The Spivak Connection — Polynomial Functors and Operads

**Timeline:** 2027+ (post-journal submission)  
**Effort:** ~3 months exploration + ~3 months formalization (research-level)  
**Publishable as:** Standalone paper bridging systems ontology and applied category theory  
**Risk:** High — genuinely open research, may not work out  

### 3.1 Mobus's Boundary as a Polynomial Functor

**The insight:** Spivak's polynomial functors framework (2022) models systems as:

$$p(y) = \sum_{i \in I} y^{B_i}$$

where I is the set of "positions" (interface types) and B_i is the set of "directions" (possible interactions at interface i). A system with input ports and output ports, each with specified types, IS a polynomial functor.

Mobus's system has:
- **Boundary B** with interfaces: positions in the polynomial
- **Input flows / output flows**: directions at each position
- **Protocols**: the wiring that connects polynomial functors

The 8-tuple ⟨C, N, G, B, T, H, Δt, ?⟩ decomposes as:
- **B** (boundary) → positions of the polynomial
- **G** (external bipartite graph) → directions at each position (what flows through each boundary port)
- **N** (internal network) → wiring diagram connecting sub-polynomials
- **T** (transformation) → the dynamical system on the polynomial

**What this buys us:** Connection to a large, active research community (Spivak, Niu, Shapiro, the Topos Institute). Mobus's informal notion of "system boundary" becomes a precise mathematical object. Composition of systems via boundary matching becomes composition of polynomial functors. This is the bridge between Bunge/Mobus systems ontology and the applied category theory world.

**CatLab.jl exploration:**
- CatLab.jl doesn't have polynomial functors natively, but has wiring diagrams
- Model Mobus systems as wiring diagram boxes
- Test composition: does connecting two Mobus systems via shared boundary give the right Mobus system?
- AlgebraicDynamics.jl (same ecosystem) handles dynamical systems on wiring diagrams

**Lean formalization:**
- No mature Lean polynomial functor library exists yet
- May need to build basic infrastructure or wait for community development
- Alternative: formalize the specific polynomial structure of Mobus systems without the full general theory

### 3.2 System Assembly as Operad Algebra

**The insight:** Bunge's Fig 1.4 shows two systems merging. The result isn't just the union of components — new bonds emerge, the environment changes, structure transforms. This is a **colimit** in the category of systems, but a special kind: the way systems compose is governed by how their boundaries match up.

An **operad** describes composition patterns. An **operad algebra** says what composes according to those patterns. The claim:

- There's an operad **SysComp** whose operations describe "ways to wire n systems together"
- The category of Bunge systems is an algebra over this operad
- Specific compositions (fusion, merger from Fig 1.4) are specific operations in the operad
- Emergent properties = what's in the colimit that's not in the components

**What this buys us:** Bunge's philosophical claim that "systemicity is not conserved" (§1.6: "the set of all systems has no algebraic structure — not even the rather modest one of a semigroup") becomes a precise statement: the category of systems is NOT a monoid (no binary operation that always produces a system), but it IS an operad algebra (composition is possible when boundary conditions match). This is a categorical correction of Bunge — he was right that there's no semigroup structure, but wrong (or imprecise) that there's "no algebraic structure." There's operadic structure.

**CatLab.jl exploration:**
- CatLab.jl has operads and operad algebras (undirected wiring diagrams)
- Define system composition operations
- Test: does composing two test systems via shared boundary give the expected result?
- This is the most speculative but potentially highest-impact exploration

**Lean formalization:**
- Operads in Lean are not well-developed in Mathlib
- Likely needs custom development
- But the specific operad (finitely many composition patterns) might be tractable

### 3.3 The Nester-Lambert Bridge (Speculative)

**The dream:** Nester gives the algebraic structure of transactions (SMC). Lambert gives the logical structure of consensus (topos). Can the categorical framework connect them?

The BRA sits between: it characterizes computational power under conservation. The categorical structure from Phase 2 (Btc as monoidal category, collapse functor) is on Nester's side. Lambert's topos-theoretic consensus lives in a different world.

**Possible connection:** The category of BRA states, equipped with the reachability relation, might form a **site** (a category with a Grothendieck topology). The sheaf condition on this site might connect to Lambert's forcing semantics. This is genuinely open research.

**What this buys us:** If it works, it connects three independent categorical frameworks for blockchain: structure (Nester), computation (BRA), consensus (Lambert). This would be a significant contribution to categorical cryptoeconomics.

**CatLab.jl exploration:**
- Unclear whether CatLab.jl can help here — sites and toposes are outside its current scope
- May need to work purely on paper and in Lean

### Phase 3 Deliverables (Speculative)

| Deliverable | Venue | Content |
|---|---|---|
| Mobus system as polynomial functor | ACT (Applied Category Theory) conference | §3.1 |
| Operadic system composition | Journal paper | §3.2, correction/extension of Bunge |
| Nester-Lambert bridge | Workshop paper or open problem | §3.3, if it works |

---

## Phase 4: Joslyn's Semantic Control Systems — The Fourth Vertex

**Timeline:** Post-thesis (2026 H2+)
**Effort:** ~2 weeks analysis + ~3 weeks formalization
**Publishable as:** Section in ISSS/AITP paper, or standalone note on the extended diagram
**Risk:** Medium — the Joslyn→Klir projection is clean; the Joslyn→Bunge mapping has a genuine ontological disagreement about environment-as-primitive vs. environment-as-derived

### Context

Cliff Joslyn (1995) "Semantic Control Systems" builds a theory of control from first principles, synthesizing Mesarovic's structuralist view with Ashby/Spencer-Brown constructivism. Joslyn was Klir's protégé; Mobus cites Klir but not Joslyn. This creates a fourth vertex in the ontological diagram with a distinct relationship pattern.

**Source:** `docs/refs/joslyn-1995-semantic-control-systems.md` (full text) and `.pdf`

### 4.1 JoslynSystem Definition

**✓ RESOLVED (2026-07-10, `Systems/Joslyn/JoslynSystem.lean`).** `JoslynSystem ι X` (indexed, Def 5) + binary `JoslynSystem₂ α`, with Def 21 constraint `C = Sᶜ` on both. **Foundational finding**: `compl_constraint` (`Cᶜ = S` — the synthetic definition's faithfulness) is essentially CLASSICAL — double complement is double-negation elimination, so "a system IS its constraint" is a theorem of classical set theory only; a constructivist passes from system to constraint but not faithfully back. The projection theorems (§4.3) are by contrast axiom-FREE.

Joslyn's System₁ (Def 5) is Mesarovic's relational system:

```
S ⊆ X₁ × X₂ × ... × Xₙ, S ≠ ∅
```

With:
- **Dimensional variety** (n): number of distinct parts/dimensions
- **Cardinal variety** (|S|): constrained states within the product space
- **Constraint** C = X - S: what the system excludes
- **Synthetic definition** (Def 21): "A system is a cardinal distinction on a variety of dimensional distinctions"

**Lean formalization target:**

```lean
structure JoslynSystem (ι : Type*) (X : ι → Type*) where
  states : Set (∀ i, X i)       -- S ⊆ ∏ Xᵢ
  nonempty : states.Nonempty     -- S ≠ ∅
```

Or the simpler binary version matching the paper's examples:

```lean
structure JoslynSystem₂ (α β : Type*) where
  states : Set (α × β)
  nonempty : states.Nonempty
```

### 4.2 Control₁ and Control₂ Hierarchy

**✓ RESOLVED — tractable core (2026-07-10, `Systems/Joslyn/Control.lean`).** Layered shape, frozen from the 1995 text in a sketch session: `Control₁` (Def 25, envelope form with the §3.3.1/§3.3.2 dissociation/overconstraint guards), `Control₂` (Def 28 — a nonempty region surviving inside every induced envelope; "constrained₂" = reduced second-order variety, not eliminated), and `Control₂Realized` (Prop 29's decomposition as data: disturb h, effect g, `compensates`). Coherence theorems: `cancellation` (the "variation of C and O_E cancel" line, axiom-free), `toControl₂` (the realization is control₂ on the controlled variables — the Marken face, not E × I), `toControl₁` (Prop 29's inner claim, axiom-free). **Governance bridge**: `Homeostat.toControl₂Realized` — every perfect (one-tick) regulator realizes control₂, machine-checking "the Joslyn formalization IS the Governance formalization"; asymptotic version deferred (needs dynamics). **DEFERRED on Mesarovic 1964 p.14**: the existence direction of Prop 29 (every control₂ admits a decomposition) — same posture as Lawvere for #10. **Foundational finding (pairs with §4.1's)**: the initial `Classical.choice` pulls were proven INCIDENTAL — `Set.singleton_ne_univ`, `Eq.ge`-via-order-instance, and `Set.biUnion_singleton` are classical in Mathlib but have elementary axiom-free replacements (`singleton_ne_univ'`, membership transport, two-inclusion proof); all five results are choice-free. With §4.1's LEM-essential `compl_constraint`, both directions of the essential-vs-incidental question are now demonstrated in this repo.

Joslyn's core contribution — two levels of control:

- **Control₁**: Passive constraint. C acts on O, constraining O's state space. Stability, equilibrium. The ball rolls to the valley floor.
- **Control₂**: Active constraint maintenance. The constraint on O is maintained *invariant despite environmental variation*. Requires internal states, feedback, semantic relations.

Control₂ decomposition: `CS = ⟨C, O = ⟨O_E, O_I⟩⟩`
- O_I: controlled variables (perception, internal state)
- O_E: effector/regulator (action, output)
- C: global environment (source of disturbances)
- f: O_I → O_E (the semantic coding — a *rule*, not a *law*)

**Lean formalization target:**

```lean
structure Control₁ (α : Type*) where
  controller : Set α    -- C
  controlled : Set α    -- O
  constraint : controller → controlled → Prop

structure Control₂ (α : Type*) extends Control₁ α where
  internal : Set α      -- O_I (controlled variables)
  effector : Set α      -- O_E (regulator)
  feedback : internal → effector  -- f: the semantic coding
  -- Key property: constraint on O_I invariant under C variation
```

### 4.3 Projection to Klir (Clean)

**✓ RESOLVED (2026-07-10, same file).** `JoslynSystem₂.toKlir` (things = full carrier, relation = states) with partial section `KlirSystem.toJoslyn₂` (requires `relation.Nonempty`). **THE SEAM, machine-checked** (`mem_range_toKlir_iff`, axiom-free): a Klir system is in the image of the Joslyn projection **iff** its relation is nonempty and its thing-set is the full carrier — Joslyn's Def 5 excludes exactly Klir's degenerate systems (empty relation) and partial carriers. First machine-checked divergence on the Joslyn edge of the diagram; both §4.3 bridge theorems are fully constructive (no axioms at all).

The Joslyn→Klir projection is straightforward — Joslyn explicitly builds on Mesarovic/Klir:

```
toKlir : JoslynSystem → KlirSystem
  things := ⋃ᵢ Xᵢ          -- flatten dimensional distinctions to T
  relation := {(a,b) | ⟨...,a,...,b,...⟩ ∈ S}  -- project constraint to R
```

**Information loss (characterized):**
1. Control₁/Control₂ distinction (constraint as passive vs. actively maintained)
2. Semantic relations (rule-following, meaning, codes)
3. Hierarchical decomposition CS = ⟨C, ⟨O_E, O_I⟩⟩
4. Dimensional structure (which Xᵢ each element belongs to)
5. Metasystem construction (environment as derived, not primitive)

**Expected proof difficulty:** Low — the Klir core is a simple projection. Should be ~50-80 lines.

### 4.4 Partial Mapping to Bunge (Non-Functorial)

**✓ RESOLVED (2026-07-11, `Systems/Joslyn/BungeMap.lean`).** All choice-free (`toBunge`, `toBunge_ne_of_env_ne`, `support_mono` fully axiom-free). Three refinements over the plan below:

1. **TWO seams, not one.** The sketch found a second obstruction hiding in the roadmap's `h : ...`: Bunge Def 1.1 demands `bondage_nonempty` (two distinct *Bonded* components), but `ActsOn` is abstract and Joslyn Def 5 states are pure relation. `toBunge` takes `env + hdisj` (the environment seam) **and** `hbond` (the action-semantics seam) as external inputs. Carrier discipline: composition = `JoslynSystem₂.support` (elements appearing in states), structure = the states themselves.
2. **The non-functoriality witness landed** (§4.6 item 3): `joslyn_toBunge_not_canonical` — one Joslyn system on `Fin 3` (states `{(0,1)}`), two admissible environments (`∅` vs `{2}`), two different Bunge systems. The map is not a function of J alone.
3. **The conditional result has exact formal shape**: `toBungeDerived` (env := `supportᶜ`, Joslyn-style derivation) is canonical, and `toBungeDerived_subsystem` shows it is **monotone from states-inclusion into Bunge's Subsystem partial order** (C ⊆ / E ⊇ / S ⊆ line up perfectly with Def 1.6) — a functor between the poset categories. "Would be a functor if E were derived", machine-checked.

Foundational note: classicality predicted ABSENT during the sketch (positive-membership route, no double complement) and confirmed — the derived-environment leg is the *constructive* complement direction, in pointed contrast to Def 21's LEM-essential `compl_constraint` one file over. Two incidental `Classical.choice` pulls (`Set.inter_compl_self`, `Set.Nonempty.ne_empty`) eliminated by membership-level rewrites (run-4 method).

The Joslyn→Bunge mapping is *not* a functor in the categorical sense, due to an ontological disagreement:

| Concept | Joslyn | Bunge |
|---|---|---|
| Environment | **Derived**: C = X - S (constraint = what the system excludes) | **Primitive**: E is given alongside C and S in the CES triple |
| Status | Emergent from the act of drawing a cardinal distinction | Independent field, constrained only by C ∩ E = ∅ |

In Joslyn, the environment is *determined* by S and X. In Bunge, E is independent of C and S. This is a genuine ontological disagreement, not notational.

**Lean formalization target:** A partial map with explicit documentation of where it fails to be functorial:

```lean
-- This is NOT a functor — it's a structure-preserving map
-- that requires choosing an environment
noncomputable def toBunge [ActsOn α]
    (sys : JoslynSystem₂ α α)
    (env : Set α)  -- must be supplied externally!
    (h : ...) : ConcreteSystem α := ...
```

**The key theorem to prove:** The Joslyn→Bunge map *would* be a functor if Bunge's environment were derived (C = X - S). Document this as a conditional result.

### 4.5 Structural Isomorphism with Mobus HCGS

**✓ RESOLVED (2026-07-11, `Systems/Joslyn/HCGS.lean`).** All choice-free; `toCoupled`, `toCoupled_combinedLaw`, and `fast_ops_is_level_homeostat` fully axiom-free. Formalized against the REAL structures (`TwoLevelGovernance` + `TimescaleDecomposition`; the pseudo-code `HCGSDecomposition α` below never existed). Three results:

1. **Convergence, level anatomy**: `levelRealizes` — each HCGS level, as a perfect homeostat, realizes Joslyn's control₂ through run 4's Governance bridge; `levelRealizes_stableI` — its maintained region is exactly the fed-down set point (definitional).
2. **Convergence, timescale**: Joslyn Def 28's "hierarchically distinct level, slower time scale" ≡ `TimescaleDecomposition`, machine-checked: packaging the HCGS as coupled dynamics (`toCoupled`, coherence `toCoupled_combinedLaw = rfl`), the frozen-coordinator fast dynamics IS the level homeostat's feedback law (`fast_ops_is_level_homeostat = rfl`). The identification is definitional once both sides are packaged — as strong as an independent-convergence claim can land.
3. **A NEW divergence (not anticipated below)**: `feedDownward_moves_stable` — Mobus's feed-downward is precisely what breaks Joslyn's Prop 29 cancellation. Different coordinator states issuing different set points MOVE the maintained region; Joslyn demands it be invariant under the upper level's variation. So the coordinator is an authority that retunes, not a disturbance that is cancelled — the table's "C ↦ Strategic context" is correct *because* context ≠ coordinator. **The §4.7 narrative is now formally grounded with the divergence as a theorem, not narration** (semantic gap rule-vs-law remains docstring-only per the discipline below).

The one-tick perfect-regulator hypothesis (`hreach`) is inherited from run 4; the asymptotic version stays deferred.

| Joslyn | Mobus HCGS |
|---|---|
| O_I (controlled variables) | Operational level |
| O_E (effector/regulator) | Coordination level |
| C (environment) | Strategic context |
| f: O_I → O_E (semantic coding) | T (transforms) — but Joslyn adds *meaning* |

**The key divergence:** Joslyn adds *semantics* as a requirement for Control₂. The feedback function f is a *rule* (contingent, selected, meaningful), not a *law* (necessary, discovered). Mobus's T is purely functional.

**Lean formalization target:** Prove the structural isomorphism, then characterize the semantic gap as a property that Joslyn has and Mobus doesn't:

```lean
-- The structural isomorphism
def control₂_to_hcgs : Control₂ α → HCGSDecomposition α := ...

-- The semantic gap: Joslyn's f is a rule (contingent), not a law (necessary)
-- This is a property, not a structural difference — cannot be captured in types alone
-- Document as a docstring theorem
```

### 4.6 The Extended Diagram

The commuting triangle becomes:

```
        toBunge
Mobus -------→ Bunge
  \              |  ↑
   \ toKlir     | toKlir    Joslyn (partial, non-functorial — env disagreement)
    \            |  |
     ↘           ↓  |
       Klir ←---- Joslyn (clean projection, forgets semantics)
```

**Key results to prove:**
1. `joslyn_triangle_commutes`: Joslyn→Bunge→Klir = Joslyn→Klir (conditional on env choice)
2. `joslyn_toKlir_factors`: Joslyn→Klir factors through Mobus→Klir when control structure is present
3. Non-functoriality witness: exhibit a morphism that Joslyn→Bunge does not preserve due to environment-as-derived vs. environment-as-primitive

### 4.7 The Independent Convergence Narrative

This is the publishing angle. Three facts:
1. Joslyn (Klir's protégé) and Mobus (cites Klir, not Joslyn) independently develop hierarchical control decomposition with environment-as-constraint
2. They agree on the structural decomposition (CS = ⟨C, ⟨O_E, O_I⟩⟩ ≅ HCGS)
3. They disagree on whether the constraint is semantic (Joslyn) or purely structural (Mobus)

This is *exactly* the kind of "independent convergence with characterized divergence" that the Mobus-Bunge commuting triangle already demonstrates. Joslyn makes the triangle a square, and the non-functorial edge (Joslyn→Bunge re: environment) is where the interesting mathematics lives.

**Relevance to thesis advisor:** Formalizing Joslyn's 1995 paper in Lean — connecting it to the ontology his student is already building — creates a direct bridge between Joslyn's theoretical contribution and the modern formalization program. The commuting diagram *discovers* the precise relationship between his work and Mobus/Bunge, just as it did for Mobus and Bunge.

### Phase 4 Deliverables

| Deliverable | Venue | Content |
|---|---|---|
| JoslynSystem + Control₁/Control₂ in Lean | Systems-ontology repo | §4.1, §4.2 |
| Joslyn→Klir clean projection | Repo + paper section | §4.3 |
| Joslyn→Bunge partial map with non-functoriality witness | Paper section | §4.4 |
| Control₂ ≅ HCGS structural isomorphism | Paper section | §4.5 |
| Extended 4-vertex diagram | ISSS/journal figure | §4.6 |
| Independent convergence narrative | Paper discussion section | §4.7 |

### Phase 4 Dependencies

```
Phase 4.1 (JoslynSystem)        ── no dependencies, start here
Phase 4.2 (Control₁/Control₂)   ── depends on 4.1
Phase 4.3 (Joslyn→Klir)         ── depends on 4.1 + Phase 3 KlirSystem.lean
Phase 4.4 (Joslyn→Bunge)        ── depends on 4.1 + Phase 1 System.lean
Phase 4.5 (Control₂ ≅ HCGS)     ── depends on 4.2 + Mobus Tuple.lean
Phase 4.6 (Extended diagram)     ── depends on 4.3 + 4.4 + 4.5
Phase 4.7 (Narrative)            ── depends on all above
```

Phase 4 can begin independently of Phases 1-3 at step 4.1, but the diagram (4.6) requires Phase 1's bridge theorem and Phase 3's Klir triangle.

---

## Tool Strategy

### CatLab.jl (Exploration Layer)

**What it's good for:**
- Defining finite categories and checking functoriality on examples
- Wiring diagrams and visualization (especially for ISSS slides)
- Monoidal categories (its emphasis — perfect for Nester/BRA work)
- Petri nets via AlgebraicPetri.jl (connects to BRA construction)
- Operads and operad algebras (Phase 3)

**What it can't do:**
- Prove universal statements ("for all systems...")
- Serve as a trust anchor for publication
- Handle dependent types or complex logical properties

**Claude Code workflow with CatLab.jl:**
- Feedback loop: define → Julia catches type/domain errors → iterate → compute → visualize
- Quality: computational conjectures, not proofs
- Value: fail fast, explore structure, generate visualizations for talks
- Limitation: documentation is sparse, API has breaking changes between versions

### Lean 4 + Mathlib CategoryTheory (Certification Layer)

**What it's good for:**
- Universal statements with machine-checked proofs
- Trust anchor for publication
- Integration with existing BRA and systems formalization

**What it can't do:**
- Quick prototyping (too much infrastructure overhead)
- Visualization

**Claude Code workflow with Lean:**
- Same as existing vibe proving: generate → compiler checks → iterate
- Quality: certified theorems
- Value: publishable results

### Recommended Sequence Per Categorical Claim

```
1. Sketch on paper / in conversation (understand what you're claiming)
2. Prototype in CatLab.jl (does it even work on examples?)
3. If yes → formalize in Lean (certify it)
4. If no → revise the claim, return to step 1
```

CatLab.jl is the "does this idea have legs?" filter. Lean is the "is this idea correct?" certifier. The combination is more efficient than either alone.

---

## Dependencies and Ordering

```
Phase 1.1 (thin category)     ─── no dependencies, start here
Phase 1.2 (flattening functor) ── depends on 1.1 (need source/target categories)
Phase 1.3 (three orderings)    ── depends on 1.1 (three instances of same pattern)
Phase 1.4 (bridge functor)     ── depends on 1.2 (uses Flatten functor)

Phase 2.1 (Btc/Eth categories) ── independent of Phase 1
Phase 2.2 (collapse functor)   ── depends on 2.1
Phase 2.3 (conservation nat)   ── depends on 2.2
Phase 2.4 (monoidal Btc)       ── depends on 2.1, CatLab.jl exploration helps most here

Phase 3.1 (polynomial)         ── depends on 1.4 (Mobus categorical structure)
Phase 3.2 (operads)            ── depends on 1.1 (subsystem category exists)
Phase 3.3 (Nester-Lambert)     ── depends on 2.2 + 2.4 (collapse + monoidal)

Phase 4.1 (JoslynSystem)       ── no dependencies, can start immediately
Phase 4.3 (Joslyn→Klir)        ── depends on 4.1 + KlirSystem.lean
Phase 4.4 (Joslyn→Bunge)       ── depends on 4.1 + System.lean
Phase 4.5 (Control₂ ≅ HCGS)    ── depends on 4.2 + Tuple.lean
Phase 4.6 (extended diagram)   ── depends on 4.3 + 4.4 + 1.4 (bridge functor)
```

Phase 1 and Phase 2 can proceed in parallel. Phase 3 requires both. Phase 4 can begin independently at 4.1-4.2, but the full diagram (4.6) requires Phase 1's bridge results.

---

## Success Criteria

**Phase 1 succeeds if:** The StructureFamily findings (3, 6, 8) are restated as categorical theorems in Lean, and the ISSS talk has CatLab.jl-generated diagrams showing the functor relationships.

**Phase 2 succeeds if:** ✅ **MET (2026-02-18).** The BRA paper's limitation is closed (`collapseFunctor : BtcState ⥤ EthState`), and `collapse_not_faithful_cat` is a genuinely new result — not statable without Category instances. Additionally: `EssSurj`, `conservation_functor_obj`, and `zero_fee_conservation` proved.

**Phase 3 succeeds if:** A clear mapping between Mobus's 8-tuple and Spivak's polynomial functors is demonstrated computationally in CatLab.jl, whether or not the Lean formalization is complete.

---

## What Could Go Wrong

**Phase 1 risk: Infrastructure tax.** Wrapping thin categories in Mathlib's `CategoryTheory.Category` typeclass may require more boilerplate than the results justify. Mitigation: if the Lean infrastructure is too painful, state the categorical results as mathematical claims (backed by CatLab.jl computation) and defer formalization to Phase 2 when you have more experience.

**Phase 2 risk: Composition proof for Btc.** Showing that transaction composition is associative with all validity constraints may be significantly harder than it looks. The intermediate states need to be valid, and the conservation constraint threads through every step. Mitigation: start with a simplified Btc (no fees, no coinbase) and extend.

**Phase 3 risk: Square peg, round hole.** Mobus's 8-tuple may not map cleanly to polynomial functors. The boundary/interface structure is suggestive but the dynamics (T, H, Δt) may not have good polynomial representations. Mitigation: this is explicitly research — if it doesn't work, document why and what would need to change.
