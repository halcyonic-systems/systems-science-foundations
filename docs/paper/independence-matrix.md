# The within-block independence matrix

Source: `Systems/Principles/Matrix.lean` (builds green with `lake build Systems.Principles.Matrix`, 2026-09-03). Every theorem cited below exists in that file; its `#print axioms` profile is in its docstring and is a subset of {`propext`, `Classical.choice`, `Quot.sound`}. Nothing uses `sorryAx`. Nothing in `Systems.lean` or `Systems/Principles.lean` was changed.

## Frame

The eight axiom structures split by what their carrier is.

| Block | Principles | Carrier | Structure and its "dynamics" field |
|---|---|---|---|
| Component | #1 #2 #3 | a component type `α` with a relation | `ConcreteSystem α` (needs `[ActsOn α]`), `ImmediateAncestor α`, `FlowNetwork α κ` |
| State | #4 #6 #8 #11 #12 | a state type `S` with a law `f : S → S` | `DynamicSystem` (`law`), `Evolution` (`step`), `Homeostat` (`feedbackLaw`), `Understanding` (`systemDyn`), `Improvement`/`DirectedAgent` (`dyn`) |

"A ⇏ B" is a concrete carrier with an A-instance and a proof that no B-instance exists on it. All 6 ordered component pairs and all 20 ordered state pairs were attempted. The 30 cross-block pairs are blocked on the component–state bridge (a `DynamicSystem` carries a `ConcreteSystem`, but nothing in the library says which state types a given component structure admits); that is a design decision, not a proof gap.

**The tied convention (state block).** Four of the five state structures are inhabited on every carrier if their dynamics is free: `Evolution` with `step := id`, `Homeostat` with an ignored set point, `DynamicSystem` with `law := id`, `Improvement` for any law that moves something. Read untied, every A ⇏ B cell in the block is either trivially true or trivially false. So each state cell fixes ONE law `f` on the carrier and asks whether each structure exists *with its dynamics equal to `f`*, the way the library's own witnesses are already stated (`cyclic3_no_understanding` fixes `systemDyn`). The five tied predicates, defined in the file:

| # | Predicate | Reads as | Non-degeneracy it carries |
|---|---|---|---|
| #4 | `Moving f` | some state moves | the whole content of #4 once the law is fixed |
| #6 | `EvolvesBy f` | `f` is the `step` of an `Evolution` for *some* fitness preorder on `S`, with a strict climb somewhere | `Evolvable`-style strictness, quantified over orders |
| #8 | `Governs f` | `f` is the `feedbackLaw` of a homeostat that is neutral at its set point (the two hypotheses of `target_is_equilibrium`) and effective (corrects some off-target state onto target in one tick) | neutrality + effectiveness; without them `Homeostat.ofLawAt` makes every law a feedback law |
| #11 | `Understood f` | some `Understanding S M` has `systemDyn = f` | `compresses`, `nontrivial` (already in the structure) |
| #12 | `Improved f` / `Directed f` | some `Improvement S` has `dyn = f` / some `DirectedAgent S M` has `understanding.systemDyn = f` | `genuine` (already in the structure); `Directed` also carries an understanding |

Ambient instances a target needs (a `Preorder` for #6, an `ActsOn` for #1) are quantified universally when they belong to the target and chosen when they belong to the source. Where a separation only exists because a degenerate ambient instance was chosen, the cell says so.

## The 8×8 table

Row = A (has an instance), column = B (no instance). Legend: **W** witnessed (theorem), **D** derivable (theorem or def realizing B from A), **NS** not statable, **X** cross-block, blocked. Superscripts: ᶜ separation is by cardinality only (dies on larger carriers, see findings); ᵃ separation depends on choosing a degenerate ambient instance; ᵇ bare `Improvement`; ᶠ full `DirectedAgent`.

| A \ B | #1 Sys | #2 Hier | #3 Net | #4 Dyn | #6 Evo | #8 Gov | #11 Und | #12 Imp |
|---|---|---|---|---|---|---|---|---|
| **#1 Sys** | — | D `ConcreteSystem.toImmediateAncestor` (vacuous target) | D `ConcreteSystem.toFlowNetwork` + `toFlowNetwork_edges_nonempty` | X | X | X | X | X |
| **#2 Hier** | Wᵃ `sep_hierarchy_systemness`; Wᶜ `sep_hierarchy_systemness_unit`; D under induced action `ImmediateAncestor.toConcreteSystem` | — | Wᶜ `sep_hierarchy_networks`; D if acyclic `ImmediateAncestor.toFlowNetwork` | X | X | X | X | X |
| **#3 Net** | Wᵃ `sep_networks_systemness`; D under induced action `FlowNetwork.toConcreteSystem` | D `FlowNetwork.toImmediateAncestor` (vacuous target) | — | X | X | X | X | X |
| **#4 Dyn** | X | X | X | — | W `sep_dynamics_evolution` | W `sep_dynamics_governance` | W `sep_dynamics_understanding` | Dᵇ `improved_iff_moving`; Wᶠ `sep_dynamics_directed` |
| **#6 Evo** | X | X | X | D `moving_of_evolvesBy` | — | W `sep_evolution_governance` | Wᶜ `sep_evolution_understanding`; D on finite ≥3 `understood_of_evolvesBy_finite` | Dᵇ `improved_of_moving`; Wᶜᶠ `sep_evolution_directed`; Dᶠ on finite ≥3 `directed_of_evolvesBy_finite` |
| **#8 Gov** | X | X | X | D `moving_of_governs` | D `evolvesBy_of_governs` | — | Wᶜ `sep_governance_understanding`; D on finite ≥3 via `directed_of_governs_finite` | Dᵇ `improved_of_moving` (and `Homeostat.toImprovement`); Wᶜᶠ `sep_governance_directed`; Dᶠ on finite ≥3 `directed_of_governs_finite` |
| **#11 Und** | X | X | X | W `sep_understanding_dynamics` | W `sep_understanding_evolution` | W `sep_understanding_governance` | — | W (bare and full) `sep_understanding_improvability`; D given motion `directed_of_understood_moving` |
| **#12 Imp** | X | X | X | D `moving_of_directed` | W `sep_improvability_evolution` | W `sep_improvability_governance` | D `understood_of_directed` (by construction) | — |

Cell count: 26 attempted. 18 carry a witness theorem, 8 are pure derivations (2 of them into a vacuous target); several cells carry both a witness and a derivation because the verdict flips with the reading (ambient choice, carrier size, bare vs full #12). No cell is NS: every within-block pair was statable once the tied convention fixed the reading.

## The witness carriers

| Carrier | Law | Holds | Fails | Cells |
|---|---|---|---|---|
| `Bool`, `noAction` | — | lineage `false ≺ true`; one flow `false → true` | `ConcreteSystem` | (#2,#1) (#3,#1) |
| `Unit` | — | reflexive ancestry | `ConcreteSystem` (any `ActsOn`); any `FlowNetwork` edge | (#2,#1) (#2,#3) |
| `Bool` | `not` | Moving, Improvedᵇ | EvolvesBy, Governs, Understood, Directed | (#4,#6) (#4,#8) (#4,#11) (#4,#12ᶠ) |
| `ℕ` | `succ` | EvolvesBy, Moving, Understood (parity) | Governs | (#6,#8) |
| `Bool` | `fun _ => true` | Governs, EvolvesBy, Moving, Improvedᵇ | Understood, Directed | (#6,#11) (#6,#12ᶠ) (#8,#11) (#8,#12ᶠ) |
| `Fin 3` | `id` | Understood ("is it 0?") | Moving, Improvedᵇ, Directed, Governs, EvolvesBy | (#11,#4) (#11,#12) |
| `Fin 4` | `· + 1` | Understood (parity), Moving, Directed | EvolvesBy, Governs | (#11,#6) (#11,#8) (#12,#6) (#12,#8) |

## Every (b) and (c) cell, with its reason

There are no (c) cells. The (b) cells:

1. **#1 ⇒ #2, #3 ⇒ #2** (vacuous target). `ImmediateAncestor α` is one Prop-valued relation with no law; `⟨fun _ _ => False⟩` inhabits it on every carrier, so no A ⇏ #2 cell can ever be witnessed as the structure stands. The data-carrying realizations (`structure'`, `toRelation`) are recorded so the derivation is not just the empty relation.
2. **#1 ⇒ #3** (`ConcreteSystem.toFlowNetwork`). A system's bond graph on its composition is a flow network: `no_self_loops` is the `a ≠ b` of `bondage_nonempty`, `edges_on` is composition membership, and the network has an edge. What #3 adds over #1 is the capacity type `κ` and nothing else. Read with `FlowNetwork.toConcreteSystem` (the other direction, under the action relation the network induces), #1's bondage and #3's directed graph are the same datum. This is the strongest component-block finding.
3. **#3 ⇒ #1 under the induced action** (`FlowNetwork.toConcreteSystem`). The witness `sep_networks_systemness` exists only because `FlowNetwork` never mentions `ActsOn`, so the two vocabularies can be filled independently. Once `actsOn a b := (a,b) ∈ net.toRelation`, a network with an edge is a system.
4. **#2 ⇒ #1 under the induced action with an off-diagonal pair** (`ImmediateAncestor.toConcreteSystem`), and **#2 ⇒ #3 given an off-diagonal pair** (`ImmediateAncestor.toFlowNetwork`). Both `Unit` witnesses use the reflexive ancestry `() ≺ ()`; an acyclicity requirement on #2 (proposed below) kills them and turns both cells into derivations.
5. **#6 ⇒ #4, #8 ⇒ #4, #12 ⇒ #4** (`moving_of_*`). A strict climb, an effective correction, and a genuine goal each name a moving state. In the tied reading, non-degenerate #4 is the weakest state-block condition and all three others imply it.
6. **#8 ⇒ #6** (`evolvesBy_of_governs`). A neutral effective homeostat's corrected state `s` lands on a fixed point `p ≠ s` and stays there, so `s` never returns; reachability is then a fitness order along which the feedback law climbs. As encoded, governance is a special case of blind evolution (fitness = "reached the set point", selection = the feedback law), not an alternative to it.
7. **#12 ⇒ #11** (`understood_of_directed`): by construction, as `DirectedAgent.toUnderstanding` already said.
8. **#4/#6/#8 ⇒ #12 bare** (`improved_iff_moving`). `Improvement.intervene` is unconstrained, so "drive straight to the goal" always works and the bare structure exists exactly when some state moves. Bare #12 coincides with non-degenerate #4. Only the full `DirectedAgent` separates from anything in the block.
9. **#6 ⇒ #11 and #8 ⇒ #11 on finite carriers with ≥ 3 states** (`understood_of_evolvesBy_finite`, via `directed_of_governs_finite`). A strict climb gives a non-periodic point, so the law is not a bijection, so (finite) not surjective, so some state is never revisited, and the two-state model "am I at the unreachable state?" with constant model dynamics is an `Understanding` per the encoding. Hence **#6 ⇒ #12 full and #8 ⇒ #12 full on finite carriers with ≥ 3 states** (`directed_of_evolvesBy_finite`, `directed_of_governs_finite`). The four `Bool` witnesses for (#6,#11), (#6,#12), (#8,#11), (#8,#12) are therefore the only kind possible on finite carriers: those separations are by cardinality, not by dynamics.
10. **#11 ∧ #4 ⇒ #12 full** (`directed_of_understood_moving`): an understanding plus any moving state is a directed agent (goal = the moving state, intervention = pin it).

## Vacuity findings

| Structure | Free instance | Theorem/def | Consequence |
|---|---|---|---|
| `ImmediateAncestor` | `⟨fun _ _ => False⟩` | `ImmediateAncestor.empty` | no cell A ⇏ #2 is statable as a non-existence |
| `FlowNetwork` | `⟨∅, ∅, _, _⟩` | (immediate) | "no network" is never true; separations use edge-nonemptiness |
| `DynamicSystem` | any law, stock component side | `DynamicSystem.ofLaw` | tied #4 = `Moving` |
| `Evolution` | `step := id` | `Evolution.trivial` | tied #6 needs a strict climb |
| `Evolvable S` | — | `evolvable_iff_exists_lt'` (Matrix.lean; `evolvable_iff_exists_lt` in Witnesses.lean is the same statement) | **`Evolvable` is a property of the fitness preorder alone**: it holds iff the order has a strict pair, whatever the dynamics. The `Evolvable (Fin 3)` half of `evolvable_but_not_improvable` is `0 < 1`; `fin3climb` plays no role in it |
| `Homeostat` | sensor `id`, set point ignored, `correct := f` | `Homeostat.ofLawAt`, `ofLaw_feedbackLaw` | **every law is a feedback law**; the set point is data the loop need not read. Only the neutrality hypotheses of `target_is_equilibrium` plus effectiveness make #8 non-degenerate |
| `Improvement` | `intervene := const goal` | `improved_iff_moving` | bare #12 ⇔ non-degenerate #4 |
| `Understanding` | "am I at the unreachable state?", `modelDyn := const false` | `Understanding.ofMissingPoint` | legitimate per the encoding, predicts nothing that changes; drives finding 9 |

**On the library's flagship witness.** `evolvable_but_not_improvable` is not a single-law witness: its `Evolvable` half is about the order on `Fin 3` (see `evolvable_iff_exists_lt`) and its un-improvable half is the 3-cycle, a different law from `fin3climb`. Under the tied reading the honest #6 ⇏ #12 witness is `sep_evolution_directed` on `Bool`, and it is a cardinality witness; on finite carriers with three or more states the implication goes the other way (`directed_of_evolvesBy_finite`). The paper should not describe `evolvable_but_not_improvable` as showing that a system which evolves cannot be improved.

**The direction §9 lists as open.** `sep_improvability_evolution`: the 4-cycle admits a directed agent (parity understanding, goal `0`, pin it) and is a blind evolution under no fitness order (every point is periodic). Under the tied reading, #12 ⇏ #6 has a witness. Under the untied reading of `Evolvable` it is unprovable for a boring reason (choose any order with a strict pair).

## Proposed non-degeneracy conditions (not applied; existing structures untouched)

| Structure | Proposal | Effect on the table |
|---|---|---|
| `ImmediateAncestor` | acyclic: `¬ Ancestor x x` (or `WellFounded immediateAncestor`), matching Level.lean's "strict partial order" showcase | kills the two `Unit` witnesses; (#2,#1) becomes Wᵃ only, (#2,#3) becomes D |
| `FlowNetwork` | `edges.Nonempty` | makes "no network" statable; already what the witnesses use |
| `Homeostat` | the two neutrality hypotheses of `target_is_equilibrium` as fields, plus effectiveness | this is `Governs`; would let `Homeostat.ofLawAt` be rejected as a homeostat |
| `Understanding` | `modelDyn` not constant (the model predicts something that changes) | excludes `Understanding.ofMissingPoint`; finding 9 would need re-examination, and the 4-cycle parity understanding (`modelDyn := not`) and both library examples (`modelDyn := id`) survive |
| `Improvement` | constrain `intervene` (e.g. it must agree with `dyn` away from the goal, or be a homeostat's feedback law) | would separate bare #12 from #4 |
| `Evolvable` | tie it to a step: `∃ e, ∃ s, s < e.step s` with `e.step` the system's law | this is `EvolvesBy`; the untied form is order-only |

## What the table supports

Inside each block, with one law per carrier, every ordered pair of the eight axiom structures is either separated by a machine-checked witness or realized by a machine-checked derivation; no pair is undecided. Eighteen directed separations hold, eight directed derivations hold (plus the conditional and induced-action derivations listed above), and four of the separations (the ones from #6 or #8 into #11 or full #12) hold only on carriers with at most two states, because on finite carriers with three or more states a blind evolution or an effective homeostat already yields an understanding and a directed agent. The sentence the paper can carry is: *within each block the encoded structures are pairwise non-derivable except for the listed directions, which are derivable and now proved; the "eight independent axioms" claim is false as stated for #1/#3 (the same graph read twice), for bare #12/#4 (the same condition), and for #8/#6 (governance is an evolution), and true as a claim of pairwise non-identity supported by eighteen witnesses.* Cross-block independence remains unaddressed pending the bridge.
