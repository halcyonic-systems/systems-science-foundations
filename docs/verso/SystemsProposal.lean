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

#doc (Manual) "Foundations for Mathematical Systems Science: Seven Traditions, One Theorem" =>

%%%
authors := ["Shingai Thornton"]
%%%

*Seven independently developed definitions of "system," one shared categorical structure — machine-verified in Lean 4.*

The general systems tradition contains several set-theoretic definitions of "system." An independent study paper framing Mobus's 8-tuple as a "systematic extension" of Bunge's CES triple led to a critical question: _does Mobus actually cite Bunge?_ He doesn't. Neither references the other.

That killed the "extension" framing and opened the real question: _how are two independently developed frameworks this compatible?_ The answer turned out to be Klir. Both cite him. Both inherit $`T` = `Set α` and $`R` = `Set (α × α)` from his $`(T, R)` definition without changing the mathematical type. The formalization proves this — the commuting triangle is `rfl`.

This document presents what the formalization produced, and where it reaches its limits — limits that Joslyn's variety-theoretic and semiotic framework is precisely designed to resolve.

Every definition below is rendered three ways: typeset mathematics, English prose, and live Lean code. Hover over any Lean expression to see its type. The compiler has checked all of it.

{include 1 SystemsProposal.Introduction}

{include 1 SystemsProposal.Definitions}

{include 1 SystemsProposal.Triangle}

{include 1 SystemsProposal.Thermostat}

{include 1 SystemsProposal.Categorification}

{include 1 SystemsProposal.Frontier}
