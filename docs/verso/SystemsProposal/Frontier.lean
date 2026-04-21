import VersoManual

open Verso.Genre Manual

#doc (Manual) "The Open Frontier" =>

# What the Formalization Cannot Yet Express

**Variety.** The current formalization has no concept of $`|X|`, $`|S|`, or $`C = X - S` as a measure of constraint. Your Definitions 13, 17, 18 — dimensional variety (the number of distinct dimensions $`n`), cardinal variety (the cardinality $`|S|` bounded by $`1 \leq |S| \leq |X|`), and constraint as set subtraction — provide the measure-theoretic layer that the structural ontology lacks.

$$`S_1 \subseteq X_1 \times \cdots \times X_n, \quad C := X - S`

**The rule/law distinction.** The `ActsOn` typeclass is opaque — a `Prop`-valued binary relation. It does not distinguish between a natural law (the ball rolls downhill) and a rule (the controller turns on the furnace). Your distinction between laws and rules (1995, §4.2) is precisely what `ActsOn` collapses.

**Control₂.** The formalization can represent that the controller acts on the furnace. It cannot express *active maintenance of a dynamic equilibrium against environmental disturbance* — your Definition 28. This requires temporal reasoning and second-order constraint that the snapshot model does not support.

The Lean column is deliberately empty here. This is the gap the formalization identifies but cannot fill alone.

# What Your Framework Provides

**Dimensional and cardinal variety give the 8-tuple a measure.** Mobus's component set $`C` has dimensional variety $`n = |C|`. His capacity $`\kappa` is a cardinal variety measure on edges. Your two-axis framework (dimensional $`\times` cardinal) provides the quantitative layer.

**The constraint $`C = X - S` connects directly to Bunge's structure.** Your System₁ constraint is the complement of the system relation within the full product space. Formalizing this gives the Bunge/Mobus framework a measure of *how constrained the system is*.

**The semantic layer gives Mobus's transforms internal structure.** The transforms $`\tau` are the natural home for contingent entailments. But $`\tau` is currently parametric — an opaque type with no internal theory. Your semiotic framework provides the theory:
- $`\tau` as a *law* (necessary entailment, discovered) — gravitational acceleration
- $`\tau` as a *rule* (contingent entailment, selected from a variety) — the controller's if/then logic
- $`\tau` as a *code* (arbitrary, conventional, interpretable) — a sensor reading mapped to a command

This is the classification that makes "too hot" → "turn off furnace" a *sign*, not just a function.

# The Categorification Question

Two complementary approaches to categorical systems theory exist:

**The combinatorial approach** (your 2018 work with Purvine): start with hypergraphs, find the right category to house them. Hypergraphs generalize binary relations to $`n`-ary — exactly the step from Klir's ordered pairs to Mesarovic's full product $`\prod X_i`.

**The foundational approach** (this formalization): start from categorical principles — lenses, functors — and derive what systems must be for composition to work. The bridge factorization (Mobus → RichBunge → Bunge = Mobus → Bunge) is already a functor triangle.

The combinatorial side asks "what is the right category for my objects?" The foundational side asks "what must objects be for composition to work?" Neither is complete without the other.

# The Proposal

**What I bring:** A working formalization (~4,700 lines, zero incomplete proofs), the LLM-assisted proving methodology, and deep familiarity with Bunge and Mobus from PhD work under Mobus.

**What you bring:** The variety-theoretic framework, the rule/law distinction and the semantic-relation argument, the Mesarovic connection, and the hypergraph intuition.

The proposed next phases:

| Phase | Content |
|---|---|
| 4 | Formalize variety-theoretic definitions (Defs 13, 17, 18). Define `DimensionalVariety`, `CardinalVariety`, `Constraint` on `KlirSystem` or a new `MesarovicSystem`. |
| 5 | Formalize control₁ / control₂. Prove Proposition 29 (control₂ ⇒ O is itself a control₁ system) in Lean. |
| 6 | Connect semantic relations to transforms. Define `SemanticRelation` as contingent entailment; prove control₂ ⇒ semantic relations ⇒ signs. |

# Where the Tree Grows

The formal ontology is not the endpoint — it is the foundation for *System Language (SL)*, a formally specified, computationally executable language for systems science, implemented in BERT. SL already has 40 typed primitives, 8 composition rules (4 Lean-verified), and working models of four blockchain architectures decomposed into the same 4-subsystem cybernetic structure. The coherence constraints Lean enforces — disjointness, bipartiteness, boundary completeness — are exactly the grammar rules SL compiles from. The tree is the formal specification.

Your variety-theoretic and semiotic framework would give SL something no systems language has ever had: a formal account of *what kind of functional relation* inhabits a system — rule or law — and what that distinction implies about meaning, control, and autonomy.

The tree does not end here. It opens.
