# Retired: Protocol Convergence Letter (May 2026)

**Status: retired as an external document, 2026-07-25. Internal reference only.**
Do not circulate. Do not cite. Superseded for all outward-facing purposes.

## What this was

The first attempt to put the K ≅ **2** work in front of outside readers. Circulated
to Cliff Joslyn and Andrew Penland in late May 2026. Two files: the letter itself and
a shorter APQ framing, plus figures and rendered PDFs as sent.

## Why it is retired

**It did not do its job.** The goal was to spark engagement. With Andrew that partly
worked, though the interest arrived in a different form than the document was aiming
for. With Cliff it did not land at all. He read it as mathematics presented for its
own sake, because it led with the proof and never stated plainly what the result was
*for*. Six weeks later he independently arrived at wanting a formal cybernetics and
systems ontology, which is the problem this work speaks to directly, without
connecting it to what he had already been sent. That is a presentation failure, not a
reader failure.

**It also overclaimed.** Two specific defects, both corrected in the source tree on
2026-07-25:

- "A maximality proof (via pigeonhole) establishes that no simpler structure
  suffices." The pigeonhole lemma runs in the opposite direction, and the general
  maximality statement is not in Lean. It is also **false as stated**: faithfulness
  constrains hom-sets rather than objects, so a three-object chain embeds faithfully
  into **2**. See the module docstring in `Systems/Category/CommonCore.lean` for the
  counterexample and the candidate repair.
- "Machine-verified across 6,200 lines." The figure was stale (the tree is ~10,800
  lines across 64 files), and faithfulness of the embeddings was described as verified
  when it existed only as a comment. Faithfulness is now a theorem
  (`klirTo*_faithful`, added 2026-07-25); maximality remains open.

The `.md` files here carry corrected text. **The `.pdf` files are the versions
actually sent and have not been altered.** Keep them that way. They are the record of
what was claimed and to whom.

## What it is still good for

Internal reference while building better external presentation. Specifically it is a
worked example of the failure mode to avoid: leading with the formalism, stating the
result before stating the problem it solves, and letting a stale number sit next to a
strong claim.

The lesson carried forward: keep making the work internally checkable, and treat
outward presentation as a separate craft with its own standard. Verification and
persuasion are different artifacts and should not be the same document.

## Successors

- `docs/reference/common-core-theorem.md` for the technical statement.
- `docs/paper/axiom-table.md` for the defensible self-summary.
- Outward-facing material to be written fresh. Nothing here should be recycled
  wholesale.
