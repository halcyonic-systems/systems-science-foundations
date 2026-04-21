import VersoManual
import Systems.Examples.Thermostat
import Systems.Klir.KlirSystem

import SystemsProposal.Introduction
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

#doc (Manual) "A Formal Systems Ontology and Its Open Frontier" =>

%%%
authors := ["Shingai Thornton"]
%%%

*Klir, Bunge, and Mobus — and the layer that needs your framework.*

In summer 2025 I wrote an independent study paper to illustrate the kind of work I wanted to do in systems ontology — bringing Bunge-style philosophical rigor to Mobus's framework in service of developing System Language. You called it a down-payment and gave me thirty red-text comments marking the areas to be addressed. I framed Mobus's 8-tuple as a "systematic extension" of Bunge's CES triple. Then you asked the right question: *does Mobus actually cite Bunge?* I checked. He doesn't. Neither references the other.

That killed the "extension" framing and opened the real question: _how are two independently developed frameworks this compatible?_ The answer turned out to be Klir. Both cite him. Both inherit $`T` = `Set α` and $`R` = `Set (α × α)` from his $`(T, R)` definition without changing the mathematical type. The formalization proves this — the commuting triangle is `rfl`.

Thirteen of your red-text comments mapped directly to machine-checked code. Your question about the type of $`S` — *"S is a set of sets of tuples, right?"* — forced a design decision the Lean compiler settled in 146 lines and two theorems.

Now that the thesis is defended, this is the work I want to focus on. This document presents what the formalization produced, and where it reaches its limits — limits that your variety-theoretic and semiotic framework is precisely designed to resolve.

Every definition below is rendered three ways: typeset mathematics, English prose, and live Lean code. Hover over any Lean expression to see its type. The compiler has checked all of it.

{include 1 SystemsProposal.Introduction}

{include 1 SystemsProposal.Definitions}

{include 1 SystemsProposal.Triangle}

{include 1 SystemsProposal.Thermostat}

{include 1 SystemsProposal.Categorification}

{include 1 SystemsProposal.Frontier}
