import VersoManual

open Verso.Genre Manual

#doc (Manual) "Introduction" =>

Mobus proposes that the language of systems should possess

> "both the characteristics of a natural language for expressing systems and the characteristics of a formal language (both mathematics and computation) making it useful in constructing computer models for simulation."
>
> — Mobus (2022), Ch. 4

and that such a language should be

> "speakable" as well as "viewable" as well as "computable." People should be able to talk to each other without over-abstraction causing the loss of details and meanings that support real understanding.
>
> — Mobus (2022), p. 70

This document is not that language. It is the verification layer beneath it.

# Three Layers

Three distinct layers, each serving a different function:

1. _System Language_ (Mobus) — the speakable and viewable layer. How practitioners reason about, communicate, and diagram systems.
2. _BERT_ (Bounded Entity Reasoning Toolkit) — the computational implementation. Renders the 8-tuple as interactive models that can be built, explored, and simulated.
3. _Lean 4_ — the formal verification layer. Proves that the mathematical foundations beneath both are sound.

Lean does not replace the system language. It validates that its mathematical commitments are sound. The hard problems were not proof search — no proof required more than a few tactic steps. They were *representational*: should `ActsOn` reference `HasStateSpace`? Should `environment` be a field or derived? Should we use `Set` or `Finset`? These decisions propagate through the entire codebase and require understanding the source material, not Lean expertise.

# How to Read This Document

Every definition is rendered three ways:

- *Typeset mathematics* — the formula as published, in the author's notation
- *English prose* — what the definition means and why it matters to a systems scientist
- *Live Lean code* — the compiler-checked encoding; hover over any expression to see its type

The three registers serve different readers. A systems scientist reads the prose and checks the math. A proof engineer reads the Lean and checks the types. A philosopher reads all three and asks whether the formalization faithfully captures the original intent. Disagreements between registers are where the interesting questions live.
