import VersoManual
import Systems.Examples.Thermostat
import Systems.Klir.KlirSystem

import SystemsProposal.Introduction
import SystemsProposal.Definitions
import SystemsProposal.Triangle
import SystemsProposal.Thermostat
import SystemsProposal.Categorification
import SystemsProposal.Frontier
import SystemsProposal.Bibliography

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Systems
open Systems.Examples

set_option pp.rawOnError true

#doc (Manual) "Foundations for Mathematical Systems Science: Seven Traditions, One Theorem" =>

%%%
authors := ["Shingai Thornton"]
%%%

Systems theorists, scientists, and engineers have produced numerous formal definitions of "system" since the mid-20th century. These definitions were developed independently, in different decades, using different notation and terminology. Yet they are remarkably compatible. This document investigates how.

The main result: the irreducible categorical content shared by all seven is a single morphism — the walking arrow category **2**. A system, in the sense common to every tradition, is *relations that depend on things*. Everything else — environment, boundary, state, input, output, time, mechanism, feedback — is tradition-specific elaboration.

*Seven traditions. One shared categorical structure. Machine-verified in Lean 4.*

{include 0 SystemsProposal.Introduction}

{include 1 SystemsProposal.Definitions}

{include 1 SystemsProposal.Triangle}

{include 1 SystemsProposal.Thermostat}

{include 1 SystemsProposal.Categorification}

{include 1 SystemsProposal.Frontier}

{include 1 SystemsProposal.Bibliography}
