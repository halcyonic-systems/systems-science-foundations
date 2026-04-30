import VersoManual

open Verso.Genre Manual

#doc (Manual) "The Open Frontier" =>

# What the Formalization Cannot Yet Express

Three gaps define the boundary of the current work. Each identifies a concept that the source texts treat as fundamental but that the Lean encoding cannot yet represent.

**Variety.** The current formalization has no concept of $`|X|`, $`|S|`, or $`C = X - S` as a measure of constraint. Joslyn's Definitions 13, 17, 18 provide the measure-theoretic layer that the structural ontology lacks: dimensional variety (how many variables a system constrains), cardinal variety (how tightly it constrains each one), and the constraint set itself as a complement within the product space.

$$`S_1 \subseteq X_1 \times \cdots \times X_n, \quad C := X - S`

**The rule/law distinction.** The `ActsOn` typeclass is opaque: a `Prop`-valued binary relation that does not distinguish between a natural law (the ball rolls downhill) and a rule (the controller turns on the furnace). A thermostat's feedback function $`f : O_i \to O_e` must be a rule (contingent entailment, not natural law); it was selected from a variety of possible control functions. Rules are arbitrary, conventional, and selected. These are exactly the properties of Peircean signs. Joslyn's distinction between laws and rules (1995, §4.2) is precisely what `ActsOn` collapses.

**Control₂.** The formalization can represent that the controller acts on the furnace. It cannot express *active maintenance of a dynamic equilibrium against environmental disturbance*, Joslyn's Definition 28. This requires temporal reasoning and second-order constraint that the snapshot model does not support.

The Lean column is deliberately empty here. This is the gap the formalization identifies but cannot fill alone.

# The Semiotic Bridge

These three gaps are not independent. Joslyn's framework connects them into a single program that gives the existing structural ontology a quantitative and semantic layer.

**Variety gives the 8-tuple a measure.** Mobus's component set $`C` has dimensional variety $`n = |C|`. His capacity $`\kappa` is a cardinal variety measure on edges. Joslyn's two-axis framework (dimensional $`\times` cardinal) provides the quantitative layer that formalizing "how constrained is this system?" requires.

**The constraint connects to Bunge's structure.** Joslyn's System₁ constraint $`C = X - S` is the complement of the system relation within the full product space. Formalizing this gives the Bunge/Mobus framework a measure of *how much* a system constrains possibility, not just *which components* it has.

**The semiotic layer gives Mobus's transforms internal structure.** The transforms $`\tau` are the natural home for contingent entailments, but $`\tau` is currently parametric: an opaque type with no internal theory. Joslyn's semiotic framework provides the theory:
- $`\tau` as a *law* (necessary entailment, discovered): gravitational acceleration
- $`\tau` as a *rule* (contingent entailment, selected from a variety): the controller's if/then logic
- $`\tau` as a *code* (arbitrary, conventional, interpretable): a sensor reading mapped to a command

This is the classification that makes "too hot" → "turn off furnace" a *sign*, not just a function. Formalizing it would give systems science something no systems language has yet expressed: the *kind* of functional relation inhabiting a system, and what that distinction implies about meaning, control, and autonomy.

# Positioning

The categorification in the previous chapter (shape categories, comparison functors, the common core theorem) is the first step of a larger program. The common core K $`\cong` *2* answers "what do all traditions share?" The open question is what the *differences* buy you.

Applied category theory has approached "what is a system?" from three directions, each with a blind spot:

**Lift one tradition** (Goguen 1978, Takahara 1985). Takahara's symbolic functor method categorified the Mesarovic tradition: systems as functors from shape categories to realization bases. Rigorous, but never engaged Bunge, Klir, Mobus, or Joslyn.

**Build from categorical scratch** (Myers 2023, Topos Institute). Lenses, double categories, the compositionality theorem. The key engineering deliverable: behaviors of composites decompose into component behaviors. But it does not engage sixty years of classical systems ontology. Myers's deterministic system is structurally identical to Wymore's at a single time step, arrived at independently; the lineage is invisible. Where Topos builds compositional frameworks from categorical primitives, this formalization extracts categorical structure from the classical definitions. The common core theorem suggests the two directions converge: the classical traditions and the categorical program are formalizing the same phenomena from opposite ends.

**Represent structure directly** (Joslyn and Purvine 2018). Hypergraphs, cellular sheaves. Generalizes binary relations to $`n`-ary, exactly the step from Klir's ordered pairs to Mesarovic's full product $`\prod X_i`.

This formalization takes a fourth approach: start from the plurality of definitions as the primary datum, construct shape categories, compute comparison functors, and extract the common core from convergence. The shape categories connect to Joslyn's structural tools (each tradition's shape is a quiver). Myers's compositionality theorem becomes more powerful when applied to richer doctrines grounded in classical ontology. Takahara's method extends naturally beyond Mesarovic through the same shape-category construction.

**A correction to Bunge.** Bunge §1.6 states: "the set of all systems has no algebraic structure, not even the rather modest one of a semigroup." He is right about semigroups: not every pair of systems can compose. But the partiality of composition *is* the structure, not the absence of it. Two systems compose when their boundaries match: a producer's output leg glues to a consumer's input leg along a shared species. The patterns of which systems can compose with which form an operad. Systems are an operad algebra: they carry structure richer than a semigroup, precisely because composition is typed by boundary compatibility rather than universally defined. Bunge diagnosed the right intuition (systems don't compose freely) but drew the wrong conclusion (therefore no algebraic structure exists). The categorical tools also extend to other domains: in a companion formalization, the collapse functor from Bitcoin's UTXO ledger to Ethereum's account-based ledger produces the first result in the project requiring category instances (non-faithfulness on hom-sets, formalizing what individual value identity means at the ledger level).

What remains open: Does the compositionality theorem generalize to doctrines that carry Bunge's mechanism, Klir's levels, or Joslyn's semiotic typing? If yes, the theorem is stronger than proven. If no, the failure is diagnostic, and publishable.

# Where This Is Going

The structural foundation is solid. The next phase is dynamics. The `myers_update_unreachable` finding identified the exact gap: Mobus captures what systems *are*, but not what they *do*. Bridging that gap means three things: formalizing Joslyn's variety measures as type-level constructions on `MobusSystem` (so systems have a quantitative constraint layer, not just a structural one); connecting the constraint equation $`C = X - S` to Bunge's structure relation (so the semiotic bridge in the previous section becomes machine-checked, not just proposed); and proving that the composition rules BERT already implements follow from the formal properties Lean already verifies.

The formal ontology grounds *System Language (SL)*, implemented in BERT (Bounded Entity Reasoning Toolkit). SL already has 40 typed primitives, 8 composition rules (4 Lean-verified), and working models of four blockchain architectures decomposed into the same 4-subsystem cybernetic structure. The coherence constraints Lean enforces (disjointness, bipartiteness, boundary completeness) are exactly the grammar rules SL compiles from. The proofs are not academic exercises; they are the reason BERT's composition rules are correct.

The tree does not end here. It opens.
