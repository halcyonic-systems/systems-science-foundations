# Systems-proposal companion (Verso) — retired 2026-07-25

## What it was
A Verso-generated companion document for the common-core result, published at
`halcyonic.systems/systems-science-foundations/` and circulated in mid-2026 to elicit
reactions. Source was `docs/verso/`; the built site was served from the `gh-pages` branch.

## Why it is retired
**It stated a claim that is false.** The document asserted that the walking arrow **2** is
the *maximal* connected structure common to the encoded traditions, and that nothing
larger is shared.

Compared as **free categories**, a three-object fork embeds into every one of the
traditions, because in a free category every path is a morphism — so a competitor enters
through a **composite that no tradition asserts** (in Joslyn's shape, via
`controller → effector → controlled`). Machine-checked as `free_category_maximality_fails`
in `Systems/Category/CommonCore.lean`.

The repaired result compares the **generating quivers** — what each tradition directly
states, rather than what its closure entails. The true statement:

> The only dependency all the encoded traditions directly assert is one. Any connected
> quiver embedding into all of them has two vertices and one edge, which is Klir's shape.

Forced by **Joslyn** (no out-degree two) and **Willems** (no in-degree two, no composable
pair); the other traditions ride along. **Existence** of the embeddings is proved (eight
named faithfulness theorems, axiom-free). **Maximality as originally stated is not proved
and is not true.**

## What it accomplished
It did the job it was written for. It went to Cliff and to Andrew and to several people
who did not reply, and the replies it did get were substantive — including Andrew's note
that every category is easily expressed as a directed labelled graph, which is the same
move the repair later made independently. Getting the reaction was the point, and the
reaction included finding the defect.

## What was done, and what was deliberately not
- The public page was replaced with a **tombstone** that states the withdrawal and the
  reason, rather than deleted. Anyone holding the link gets the correction instead of a
  404. `/verso/` and `/handout/` now 404.
- The **prior site content remains in the `gh-pages` branch history**. Nothing was erased.
- The source moves here unaltered. It is the record of what was published, and is not
  edited to match the current understanding — the same treatment given the
  protocol-convergence letter's PDFs in `docs/archive/protocol-convergence-letter-2026-05/`.

## If this is ever revived
Do not restore it as written. The maximality section is the defect; the rest of the
document predates the faithfulness proofs and the quiver reframing. A successor should
state existence as proved, state the quiver-level result as the interesting claim, and
carry the presentation-sensitivity caveat: quiver-level claims are **not** invariant under
adding derived arrows, so the theorem is relative to the documented encodings, defended by
`docs/language/terminology-concordance.md`.
