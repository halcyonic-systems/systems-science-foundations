import VersoManual

open Verso.Genre Manual

#doc (Manual) "The Open Frontier" =>

# What the Formalization Cannot Yet Express

**Variety.** The current formalization has no concept of $`|X|`, $`|S|`, or $`C = X - S` as a measure of constraint. Joslyn's Definitions 13, 17, 18 — dimensional variety (the number of distinct dimensions $`n`), cardinal variety (the cardinality $`|S|` bounded by $`1 \leq |S| \leq |X|`), and constraint as set subtraction — provide the measure-theoretic layer that the structural ontology lacks.

$$`S_1 \subseteq X_1 \times \cdots \times X_n, \quad C := X - S`

**The rule/law distinction.** The `ActsOn` typeclass is opaque — a `Prop`-valued binary relation. It does not distinguish between a natural law (the ball rolls downhill) and a rule (the controller turns on the furnace). Joslyn's distinction between laws and rules (1995, §4.2) is precisely what `ActsOn` collapses.

**Control₂.** The formalization can represent that the controller acts on the furnace. It cannot express *active maintenance of a dynamic equilibrium against environmental disturbance* — Joslyn's Definition 28. This requires temporal reasoning and second-order constraint that the snapshot model does not support.

The Lean column is deliberately empty here. This is the gap the formalization identifies but cannot fill alone.

# The Semiotic Layer

**Dimensional and cardinal variety give the 8-tuple a measure.** Mobus's component set $`C` has dimensional variety $`n = |C|`. His capacity $`\kappa` is a cardinal variety measure on edges. Joslyn's two-axis framework (dimensional $`\times` cardinal) provides the quantitative layer.

**The constraint $`C = X - S` connects directly to Bunge's structure.** Joslyn's System₁ constraint is the complement of the system relation within the full product space. Formalizing this gives the Bunge/Mobus framework a measure of *how constrained the system is*.

**The semantic layer gives Mobus's transforms internal structure.** The transforms $`\tau` are the natural home for contingent entailments. But $`\tau` is currently parametric — an opaque type with no internal theory. Joslyn's semiotic framework provides the theory:
- $`\tau` as a *law* (necessary entailment, discovered) — gravitational acceleration
- $`\tau` as a *rule* (contingent entailment, selected from a variety) — the controller's if/then logic
- $`\tau` as a *code* (arbitrary, conventional, interpretable) — a sensor reading mapped to a command

This is the classification that makes "too hot" → "turn off furnace" a *sign*, not just a function.

# Toward a Modular Categorical Definition

The categorification in the previous section — shape categories, comparison functors, the common core theorem — is the first step of a larger program. The common core K $`\cong` *2* answers "what do all traditions share?" The open question is what the *differences* buy you.

Applied category theory has approached "what is a system?" from three directions, each with a blind spot:

**Lift one tradition** (Goguen 1978, Takahara 1985): Takahara's symbolic functor method categorified the Mesarovic tradition — systems as functors from shape categories to realization bases. Rigorous, but never engaged Bunge, Klir, Mobus, or Joslyn.

**Build from categorical scratch** (Myers 2023): lenses, double categories, the compositionality theorem. The key engineering deliverable — behaviors of composites decompose into component behaviors. But it does not engage sixty years of classical systems ontology. Myers's deterministic system is structurally identical to Wymore's at a single time step, arrived at independently; the lineage is invisible.

**Represent structure directly** (Joslyn and Purvine 2018): hypergraphs, cellular sheaves. Generalizes binary relations to $`n`-ary — exactly the step from Klir's ordered pairs to Mesarovic's full product $`\prod X_i`.

The comparative program demonstrated in this formalization takes a fourth approach: start from the plurality of definitions as the primary datum, construct shape categories, compute comparison functors, and extract the common core from convergence. The shape categories connect to Joslyn's structural tools (each tradition's shape IS a quiver). Myers's compositionality theorem becomes more powerful when applied to richer doctrines grounded in classical ontology. Takahara's method extends naturally beyond Mesarovic through the same shape-category construction.

What remains open: Does the compositionality theorem generalize to doctrines that carry Bunge's mechanism, Klir's levels, or Joslyn's semiotic typing? If yes, the theorem is stronger than proven. If no, the failure is diagnostic — and publishable.

# Open Research Directions

**Variety and constraint.** Formalize Joslyn's dimensional and cardinal variety (Defs 13, 17, 18) as type-level constructions on `KlirSystem` or a new `MesarovicSystem`. This gives the structural ontology a *quantitative* layer — how constrained a system is, not just what its parts are.

**Control and autonomy.** Formalize control₁ / control₂ (Joslyn 1995). Prove Proposition 29 — that a control₂ system's output is itself a control₁ system — in Lean. This is the formal content of "autonomy" in the systems tradition.

**Semantic relations.** Connect contingent entailment to Mobus's transforms. The transforms $`\tau` are currently opaque type parameters. Enriching them with Joslyn's rule/law/code classification would formalize what no systems language has yet expressed: the *kind* of functional relation inhabiting a system, and what that distinction implies about meaning and control.

# Where the Tree Grows

The formal ontology is not the endpoint — it is the foundation for *System Language (SL)*, a formally specified, computationally executable language for systems science, implemented in BERT. SL already has 40 typed primitives, 8 composition rules (4 Lean-verified), and working models of four blockchain architectures decomposed into the same 4-subsystem cybernetic structure. The coherence constraints Lean enforces — disjointness, bipartiteness, boundary completeness — are exactly the grammar rules SL compiles from. The tree is the formal specification.

Joslyn's variety-theoretic and semiotic framework would give SL something no systems language has ever had: a formal account of *what kind of functional relation* inhabits a system — rule or law — and what that distinction implies about meaning, control, and autonomy.

The tree does not end here. It opens.
