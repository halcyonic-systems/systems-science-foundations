import VersoManual
import Systems.Examples.Thermostat
import Systems.Klir.KlirSystem

import SystemsProposal.Definitions
import SystemsProposal.Triangle
import SystemsProposal.Thermostat
import SystemsProposal.Categorification
import SystemsProposal.Frontier

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Systems
open Systems.Examples

set_option pp.rawOnError true

#doc (Manual) "Foundations for Mathematical Systems Science: Seven Traditions, One Theorem" =>

%%%
authors := ["Shingai Thornton"]
%%%

Systems theorists, scientists, and engineers have produced numerous formal definitions of "system" since the mid-20th century. These definitions were developed independently, in different decades, using different notation and terminology. Yet they are remarkably compatible. This document investigates how. It examines seven traditions spanning six decades: three set-theoretic (Klir, Bunge, Mobus) and four that require categorical language (Myers, Wymore, Mesarovic, Joslyn).

The main result: the irreducible categorical content shared by all seven is a single morphism — the walking arrow category **2**. A system, in the sense common to every tradition, is *relations that depend on things*. Everything else — environment, boundary, state, input, output, time, mechanism, feedback — is tradition-specific elaboration.

The Topos Institute has called this program "pioneering a mathematical systems science." This formalization takes a complementary approach: rather than building new categorical frameworks, it starts from the plurality of classical definitions and discovers their shared structure through machine verification.

*Seven traditions. One shared categorical structure. Machine-verified in Lean 4.*

The investigation began with a 2025 independent study paper (Thornton, SSCI independent study, Binghamton University, 2025) that framed Mobus's 8-tuple as an extension of Bunge's CES triple. A simple question — does Mobus cite Bunge? — encouraged investigation into the eerie similarities. He doesn't. Neither references the other. Two researchers, 43 years apart, arrived at structurally compatible frameworks without knowing each other's work.

The answer turned out to be Klir. Both cite him. Both inherit $`T` = `Set α` and $`R` = `Set (α × α)` from his $`(T, R)` definition without changing the mathematical type. The formalization proves this — the two paths from Mobus back to Klir, one through Bunge and one direct, produce identical results.

This document presents what the formalization produced, and where it reaches its current limits.

We begin with the three set-theoretic definitions (Klir, Bunge, Mobus) in Chapters 1–2, then extend to all seven via shape categories in Chapter 3.

Every definition below is rendered three ways:

- *Typeset mathematics* — the formula as published, in the author's notation
- *English prose* — what the definition means and why it matters to a systems scientist
- *Live Lean code* — the compiler-checked encoding; hover over any expression to see its type

The three registers serve different readers. A systems scientist reads the prose and checks the math. A proof engineer reads the Lean and checks the types. A philosopher reads all three and asks whether the formalization faithfully captures the original intent. Disagreements between registers are where the interesting questions live.

The Lean 4 proof assistant has verified every claim — if a statement compiles, it is logically valid. No claim in this document is taken on trust.

A note on the Lean blocks: `#check` displays the type of a definition — think of it as asking "what kind of thing is this?" The `@` prefix makes all arguments explicit. A `structure` in Lean is a record type with named fields — the formal analog of a mathematical definition with components. An `example` constructs a concrete inhabitant, proving the definition is not vacuously satisfiable. You do not need to read Lean to follow this document, but hovering over any expression reveals its type, and every type tells you something about the mathematics.

{include 1 SystemsProposal.Definitions}

{include 1 SystemsProposal.Triangle}

{include 1 SystemsProposal.Thermostat}

{include 1 SystemsProposal.Categorification}

{include 1 SystemsProposal.Frontier}
