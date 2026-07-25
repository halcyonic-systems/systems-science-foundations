# APQ: Does the Common Core of Systems Also Describe the Common Core of Protocols?

*Submitted to SIGFPT by Shingai Thornton, Halcyonic Systems*
*May 2026*

---

## Empirical Context

Four protocols from independent domains, each an observable coordination system with a documented rule set:

- **TCP/IP** (networking) — reliable delivery from sender to receiver via sequencing, acknowledgment, retransmission.
- **Bitcoin** (consensus) — valid transactions from proposer to confirmed ledger via proof-of-work.
- **REST APIs** (software interfaces) — requests from client to server via constrained verbs, responses back.
- **Hand-washing** (public health) — contamination from contact-state to resolved-state via a constrained physical procedure.

The question is whether these share formal structure, or only a family resemblance.

## Key Dimension

*Formalizability.* Seven independently developed formal definitions of "system" (Klir 1969, Bunge 1979, Mobus 2022, Myers, Wymore, Mesarovic, Joslyn) were recently formalized in Lean 4 and shown to share one irreducible categorical structure: the walking arrow (category **2**), a single directed dependency. The result, K ≅ **2**, is formalized across roughly 10,800 lines with zero unresolved proof obligations and no custom axioms, and the convergence was discovered through the formalization rather than assumed. Melanie Swan's "Categorical Cryptoeconomics" (2024) independently established rich categorical structure in blockchain protocols. The open dimension is whether that structure is general: whether protocols across domains constitute a category in the mathematical sense, which would resolve Rao's wager — "do protocols constitute a genuine kind?" — affirmatively.

## Precise Question

> **Does the common core of formal system definitions (K ≅ 2) also describe the common core of protocols? Specifically: can protocols from independent domains each be instantiated as systems in the Klir/Bunge/Mobus sense, such that the walking arrow embeds faithfully into each instantiation and the categorical structure — composition, governance, layering — transfers?**

The Protocol Institute's own definitions already have the right shape. Rao's "metabolization of human behaviors into coordination infrastructure" and Stinson-Schroff's "engineered arguments as predefined rule sets over actors" both name things with directed dependencies between them — the same shape as Klir's things-and-relations definition of a system. The question is whether that shape survives formal instantiation across domains, or breaks.

## Why This APQ Matters

If protocols are systems in the formal sense, protocol theory inherits a body of machine-verified results rather than rebuilding them: composition that closes without compatibility preconditions, governance modeled as homeostatic feedback with a provable fixed point, session semantics as composable lenses, and layering that yields time-scale separation. These transfer as theorems, not analogies.

If protocols are *not* systems — if some protocol-specific structure resists the embedding — locating that structure is equally valuable: it names precisely what protocols add beyond the common core. The Joslyn cyclic feedback shape (the only tradition with cycles, and the natural home for protocol execution loops) is the leading candidate; composing cyclic systems requires traced monoidal categories the current formalization does not yet address. Either answer advances both programs.

## Sketch of an Approach

1. Take the four protocols above.
2. **Start from Mobus.** For each, construct the 8-tuple — components, internal network, environment, external flows, boundary, transforms, history, timescale. The 8-tuple carries the most structure, so protocol-specific detail is recorded before any reduction.
3. Apply the existing bridge map (Mobus → Bunge → Klir) and verify the walking arrow embeds faithfully at the **2** floor.
4. Test the proven theorems against the instances. Concretely, model **Bitcoin difficulty adjustment as a homeostat** — set point = 10-minute block interval, sensor = observed inter-block times, error = deviation over the 2016-block retarget window, corrective law = difficulty adjustment — and check that the homeostatic fixed-point theorem predicts the convergence difficulty adjustment exhibits empirically. Likewise: does TCP + HTTP compose unconditionally?
5. Identify any protocol-specific structure the 8-tuple does not capture. This residue — the difference between the rich instantiation and the reduced core — is the research contribution.

Steps 1–4 are tractable with current LLM-assisted Lean 4 methodology (cf. DeepMind's AlphaProof Nexus, May 2026). Step 5 is where new theory lives.

## Connection to Existing PI Themes

- **Bus bunching** ("Theorizing Protocolization II") — buses, passengers, and schedules decompose as things with directed dependencies; the bunching feedback loop is the Joslyn cyclic shape.
- **Season 4, "AI and Protocols"** — the LLM-assisted Lean methodology is the construction tool, and machine verification routes around credential-weighted argument: the compiler checks proofs, not win records.
- **Planetary Computational Tangle** — protocol tangles are system compositions, and composition is unconditional, so tangles are formally tractable rather than analytically hopeless.

This APQ is **self-contained** (investigable from the Lean codebase alone, no prior systems-science training) and **indivisible** (one question about one structural relationship). It contributes to the APQ set's representativeness by spanning the formalizability dimension across four domains.

---

*Companion document: "Protocols Are Morphisms: On the Common Core of Coordination" (Thornton, 2026). The systems-science-foundations formalization is available at https://github.com/halcyonic-systems/systems-science-foundations.*
