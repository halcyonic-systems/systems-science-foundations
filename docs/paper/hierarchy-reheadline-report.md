# #2 Hierarchy re-headlined on Mobus Eq. 4.3 — full report

Branch `hierarchy-reheadline`, commit `f844124`, worktree `/Users/home/Desktop/halcyonic-projects/active/ssf-wt-hier`.
One new file: `Systems/Principles/Hierarchy.lean` (557 lines, imports `Systems.Principles.Matrix`).
`lake build Systems.Principles.Hierarchy` is green; no `sorry`; no existing file touched; nothing pushed.

## 1. The predicate

`Hierarchical σ T` (structure, indexed by a `ConcreteSystem σ` under `[ActsOn α]`, and by an ambient `[LinearOrder T] [InteractionStrength α T]`):

| Field | Content |
|---|---|
| `tree : RecursiveComponent α` | Mobus Eq. 4.3 tree |
| `atoms_eq : tree.atomSet = σ.composition` | atoms are exactly the components |
| `nested : ∃ c ∈ tree.children, c.IsComplex` | a genuine subsystem level (forces `2 ≤ tree.depth`, `Hierarchical.two_le_depth`) |
| `decomposition : tree.IsDecomposition` | every complex node has ≥ 2 children, sibling atom-sets pairwise `Disjoint`, node atoms `IsOrganized` (a bonded distinct pair — Eq. 4.3's "complex component = system") |
| `nd : NearDecomposable σ T` | Simon's condition from Level.lean, verbatim reuse |
| `modules_eq : nd.modules = tree.modules` | Simon's partition is the tree's top level |

**Content choice, documented.** Of the two options (a `NearDecomposable` instance, or acyclicity of `ImmediateAncestor`) the file takes near-decomposability. Eq. 4.3 and Mobus's sentence at `2-principles-of-systems-science.md:287` ("component interactions within the subsystem are stronger than interactions between components in other subsystems") are one claim seen from structure and from strength; acyclicity of a bare ancestry relation is Bunge's descent order and says nothing about strength. Cost: #2 acquires one ambient instance, `InteractionStrength α T`, in exactly the role `ActsOn α` plays for #1. Consequence: hierarchy as encoded is a property of the **strength profile**, not of the bond graph. `twoLevel` is hierarchical under `gradedStrength` and not under `uniformStrength`, bonds unchanged.

**Non-vacuity.** Fails: `not_hierarchical_of_uniform` (any carrier, any action, any system, uniform strength) and `not_hierarchical_bool` (two things, any action, any strength). Holds: `twoLevelHierarchical`.

## 2. Declarations

All profiles are `{propext, Classical.choice, Quot.sound}` unless noted. `Classical.choice` enters through the **definition** `RecursiveComponent.atoms` (checked: `#print axioms RecursiveComponent.atoms`; nested structural recursion over `List`, both the `flatMap` and `foldr` forms), so every statement mentioning `atomSet` inherits it regardless of proof content. Level.lean's `depth` shows `{propext, Quot.sound}`.

Bridges from `RecursiveComponent` (definitions):
- `RecursiveComponent.children` — child list (empty for an atom).
- `RecursiveComponent.IsComplex` — Prop, true on `complex`.
- `RecursiveComponent.atoms` — leaf `thing`s, left to right, as a list; complex-node labels do not appear.
- `RecursiveComponent.atomSet` — the same as a `Set α`.
- `RecursiveComponent.modules` — `children.map atomSet`.
- `RecursiveComponent.IsDecomposition` — inductive Prop (needs `[ActsOn α]`), the three per-node conditions above.
- `uniformStrength α s` — the constant profile.
- `chainActs` (`0 ▷ 1`, `1 ▷ 2` on `Fin 3`), `gradedStrength` (strength 2 between 0 and 1, else 1), `twoLevel` (the chain as a system, composition `univ`), `subTree` (`{0,1}`), `twoLevelTree` (`{ {0,1}, 2 }`), `chainNet` (flow network `0→1→2`, unit capacity).

Theorems:
- `RecursiveComponent.mem_atoms_complex` — `a ∈ (complex b cs).atoms ↔ ∃ c ∈ cs, a ∈ c.atoms`.
- `RecursiveComponent.foldl_max_depth_ge_init`, `foldl_max_depth_ge_mem` — the `foldl max` in `depth` dominates its seed and every member.
- `Hierarchical.two_le_depth` — a complex child forces `2 ≤ tree.depth`.
- `RecursiveComponent.IsDecomposition.exists_atom` — a decomposition has an atom.
- `List.exists_rel_of_pairwise` — in a pairwise-related list of length ≥ 2 every element is related to some element (profile: `propext` only).
- `RecursiveComponent.IsDecomposition.exists_two_atoms` — two distinct atoms in any complex node of a decomposition.
- `Hierarchical.exists_split` — **the content of #2**: modules `m₁, m₂` in `nd.modules`, distinct `x, y ∈ m₁`, and `z ∈ m₂` with `z ∉ m₁`. Every failure theorem spends exactly this.
- `Hierarchical.within_exceeds_between_somewhere` — for those modules, `m₁ ≠ m₂` and `strength x z < strength x y`.
- `not_hierarchical_of_uniform` — `@Hierarchical α _ σ T _ (uniformStrength α s) → False`, for every `σ` on every carrier under every `ActsOn`.
- `not_hierarchical_bool` — on `Bool`, for every action instance and every strength instance, no `Hierarchical σ T`.
- `mem_subTree_atomSet`, `mem_atomic_atomSet`, `twoLevelTree_modules` (rfl), `subTree_isDecomposition`.
- `twoLevelHierarchical : @Hierarchical (Fin 3) chainActs twoLevel ℕ _ gradedStrength` — threshold 2, modules `{0,1}` and `{2}`.
- `sep_systemness_hierarchical`, `sep_systemness_hierarchical_bool`, `sep_networks_hierarchical` — the witnessed cells (§3).
- `Hierarchical.toConcreteSystem`, `Hierarchical.toFlowNetwork`, `Hierarchical.toFlowNetwork_edges_nonempty` — the derivation cells (§3).

## 3. The six cells, recomputed

Convention of Matrix.lean: row A has an instance, column B has none. Superscripts as in the md: ᵃ = a degenerate or chosen ambient instance, ᶜ = cardinality only.

| Cell | Old verdict (Matrix.lean) | New verdict (Hierarchy.lean) |
|---|---|---|
| (#1,#2) | D `ConcreteSystem.toImmediateAncestor`, vacuous target | **W** `sep_systemness_hierarchical`: `twoLevel` is a system and under `uniformStrength (Fin 3) 1` no system on the carrier is hierarchical — the same `σ` that is hierarchical under `gradedStrength`. ᵃ in the strength. **Wᶜ** `sep_systemness_hierarchical_bool`: `lineageBool.toConcreteSystem` on `Bool`, for every `T` and every strength profile, no hierarchy. Choice-free. |
| (#2,#1) | Wᵃ `sep_hierarchy_systemness`, Wᶜ `sep_hierarchy_systemness_unit`; D under induced action | **NOT SEPARABLE, by construction**: `Hierarchical.toConcreteSystem` (the structure is indexed by `σ`). This is Eq. 4.3 read literally — `c_{i,j,l} = S_{i,j,l+1}`, a complex component IS a system — so hierarchy presupposes systemness. The old witnesses existed because `ImmediateAncestor` never asked for a bond. Deviates from the prediction that this cell would become substantively witnessed. |
| (#2,#3) | Wᶜ `sep_hierarchy_networks` (reflexive `Unit` self-ancestry); D if acyclic | **NOT SEPARABLE**: `Hierarchical.toFlowNetwork` = `σ.toFlowNetwork c`, with `Hierarchical.toFlowNetwork_edges_nonempty`. The `Unit` witness has no decomposition analogue: `exists_split` needs three components. |
| (#3,#2) | D `FlowNetwork.toImmediateAncestor`, vacuous target | **W** `sep_networks_hierarchical`: `chainNet` has an edge, and under `uniformStrength (Fin 3) 1` no system under ANY `ActsOn (Fin 3)` is hierarchical (the uniform failure never reads bonds). Choice-free in the action, ᵃ in the strength. |
| (#1,#3) | D `ConcreteSystem.toFlowNetwork` + `toFlowNetwork_edges_nonempty` | unchanged (does not mention #2) |
| (#3,#1) | Wᵃ `sep_networks_systemness`; D under induced action `FlowNetwork.toConcreteSystem` | unchanged (does not mention #2) |

Net: #2's column goes from two vacuous derivations to two witnesses (one substantive, one cardinality); #2's row goes from three witnesses (two cardinality, one ambient-choice) to two derivations by construction. The headline finding: the strength profile, not the bond graph, decides hierarchy.

## 4. Proposed replacement for `principle2_hierarchy` (Systems/Principles.lean, NOT applied)

Current:

```lean
/-- **#2 Hierarchy** (axiom, `ImmediateAncestor`, Level.lean). The ancestor relation is
    transitive: levels stack. -/
theorem principle2_hierarchy {α : Type*} [ImmediateAncestor α] {x y z : α}
    (hxz : Ancestor x z) (hzy : Ancestor z y) : Ancestor x y :=
  ancestor_trans hxz hzy
```

Proposed (the Eq. 4.3 lines are verbatim from Level.lean's `RecursiveComponent` docstring, Lane C):

```lean
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
```

Principles.lean would also need `import Systems.Principles.Hierarchy` (or the predicate moved into Level.lean) — an import-cycle decision left to the merge, since Hierarchy.lean currently imports Matrix.lean which imports Principles.lean.

## 5. Updated three-row #2 section for `docs/paper/independence-matrix.md`

```markdown
| A \ B | #1 Sys | #2 Hier | #3 Net |
|---|---|---|---|
| **#1 Sys** | — | W `sep_systemness_hierarchical` (uniform strength, on the system that is hierarchical under `gradedStrength`; ᵃ in strength); Wᶜ `sep_systemness_hierarchical_bool` (any strength, any action) | D `ConcreteSystem.toFlowNetwork` + `toFlowNetwork_edges_nonempty` |
| **#2 Hier** | D by construction `Hierarchical.toConcreteSystem` (Eq. 4.3: a complex component is a system) | — | D `Hierarchical.toFlowNetwork` + `toFlowNetwork_edges_nonempty` |
| **#3 Net** | Wᵃ `sep_networks_systemness`; D under induced action `FlowNetwork.toConcreteSystem` | W `sep_networks_hierarchical` (uniform strength; choice-free in the action, ᵃ in strength) | — |

#2 is now `Hierarchical σ T` (Principles/Hierarchy.lean): a `RecursiveComponent` decomposition of `σ` (Mobus Eq. 4.3) with a subsystem level, every complex node a system, disjoint siblings, and `NearDecomposable` top-level modules. The ambient for #2 is `InteractionStrength α T`, in the role `ActsOn α` plays for #1; superscript ᵃ in the #2 column means "the strength profile was chosen". The vacuity-table row for `ImmediateAncestor` no longer applies to #2, and both old `Unit` witnesses are retired: a decomposition needs three components in two modules (`Hierarchical.exists_split`). Hierarchy so encoded is a property of the strength profile, not the bond graph: `twoLevel` flips between hierarchical and not with its bonds unchanged.

Witness carriers added: `Fin 3` with `chainActs` and `uniformStrength (Fin 3) 1` for (#1,#2) and (#3,#2); `Fin 3` with `chainActs` and `gradedStrength` for the positive instance `twoLevelHierarchical`; `Bool` with `lineageBool.toActsOn` and any strength for (#1,#2)ᶜ.
```

## 6. What made a clean predicate hard — the bridges that had to be defined

- **`RecursiveComponent` carries no relation to `ActsOn` or to `ConcreteSystem`.** It has a `thing : α` label per node and a child list, nothing else. "Atoms are the components" therefore needed `atoms` / `atomSet` (defined here) and the field `atoms_eq : atomSet = composition`. Simon's partition needed `modules := children.map atomSet` and the field `modules_eq`. Neither is in Level.lean.
- **An arbitrary labelled tree is not a decomposition.** Without "≥ 2 children" the chain `complex [complex [a,b,c]]` satisfies near-decomposability with one module (between-module condition vacuous). Without sibling disjointness a tree can list a component twice. Without organized atoms a complex node is not a system, contradicting Eq. 4.3's `S_{l+1}`. Hence `IsDecomposition` with the three clauses. `organized` reuses `IsOrganized` from Systemness.lean; it is the only place bonds enter #2.
- **The `thing` label of a complex node is dead data.** The carrier has no element that IS the subsystem, so `twoLevelTree` labels its subsystem with the arbitrary component `0`. Level.lean's `RecursiveComponent.thing` returns it but nothing here reads it. A faithful encoding of `S_{i,j,l+1}` as a *thing of the carrier* would need the carrier to contain its own subsystems (a Bunge-style parthood preorder), which is a design decision beyond this file.
- **`InteractionStrength` carries no relation to `ActsOn` either.** Level.lean's `NearDecomposable` never mentions bonds, so `organized` (bonds) and `nd` (strengths) are independent bridges to #1's and Simon's vocabularies; neither implies the other. That disconnect is exactly what lets the (#1,#2) witness sit on an unchanged bond graph, and is the same species of vocabulary split the md already records for `FlowNetwork` vs `ActsOn`.
- **`nested` is stated as "some child is complex", not `2 ≤ depth`.** `depth` is a `foldl max` and is painful to destructure; the file proves `two_le_depth` from `nested` (one direction only; the converse is not proved).
- **Near-decomposability applies at the top level only.** `NearDecomposable` takes a single threshold; requiring it at every complex node with one threshold contradicts across levels (a within pair at level l is a between pair at level l+1). Deeper complex nodes get organization only. Per-level thresholds would be the extension.
- **`Classical.choice` in `atoms`.** Both `List.flatMap` and `foldr (· ++ ·)` forms of the nested structural recursion pull `Classical.choice` into the definition, so every downstream profile carries it. If a choice-free profile matters, the route is a mutual definition over `RecursiveComponent` and `List RecursiveComponent`; not chased here.
- **`List.exists_rel_of_pairwise` lives in namespace `Systems`** (it is `Systems.List.exists_rel_of_pairwise`); if a Mathlib lemma of the same content exists it should replace it at merge.
