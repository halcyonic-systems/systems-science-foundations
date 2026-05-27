# ISSS 2026 Presentation Notes

*What Happens When You Type-Check Bunge*

---

## Narrative Spine

The Joslyn feedback mapping drives the talk: **"My advisor asked these questions. Here's what happened when I gave them to a proof assistant."**

Cliff's 30 red-text comments on the summer 2025 paper are the human side of the story. The Lean compiler's responses are the machine side. 13 of 30 comments map directly to formalized code. A1 — "S is a set of sets of tuples, right?" — turned out to be the most productive.

---

## Centerpiece Slide: A1 — "The Compiler Answered Back"

**This is the emotional core of the talk.** Every systems scientist in that room has had a reviewer question their formalism. None of them have had a compiler answer back. The visual contrast between informal advisor markup and machine-checked proof is what lands.

**Layout:** Split screen. Left side: Cliff's actual red-text markup from the PDF (handwritten/annotated style, informal, questioning). Right side: the Lean theorem signature (monospace, precise, verified).

Left (red-text markup — use a screenshot or faithful reproduction of the actual PDF annotation):
> "What do you mean more precisely? 'Set of relations' literally means S is a set of sets of tuples, right? So e.g. S = {S_i}. Tuples implies a Cartesian product, so is it S_i ⊆ C × E, or S_i ⊆ (C ∪ E) × (C ∪ E), or what?"

Right (Lean — cold, precise, machine-checked):
```lean
theorem flatten_internal_commutes {α : Type*} [ActsOn α]
    (r : RichConcreteSystem α) :
    ⋃₀ r.internalFamily =
    internalProjection r.composition r.flatten
```

**Punchline:** The compiler forced the exact decision Cliff was requesting — and then proved both readings are equivalent for the theorems in the paper. The advisor's informal question and the proof assistant's formal answer are about the same mathematical object. One is red ink on a PDF; the other is a machine-checked certificate.

**Production note:** Use the full A1 quote including "Tuples implies a Cartesian product, so is it S_i ⊆ C × E, or S_i ⊆ (C ∪ E) × (C ∪ E), or what?" — the specificity of Cliff's question is what makes the pairing work. He was already asking a type-theoretic question; he just didn't have a type-checker.

---

## Finding 6 Slide: The Structure Family

**Visual:** Show N (internal flow network) and G (bipartite external flow graph) as two separate relation sets, then their union ⋃₀{N, G} = `totalRelation` = Bunge's S.

**Key equation:**
```
{N.toRelation, G.toRelation}  →  ⋃₀{N.toRelation, G.toRelation}  =  totalRelation  =  S
     (Mobus's source)              (flattening)                      (Bunge's target)
```

**Punchline:** The bridge theorem IS the flattening. Mobus's N/G separation is the *source* of the structure family; Bunge's flat S is the *target*. This relationship was implicit in both frameworks but never stated until the proof assistant made it visible.

---

## Audience Calibration

**Who's in the room:** ISSS readers know Bunge and Mobus. Many have taught from Mobus's textbook. They have NOT seen Lean 4 or proof assistants.

**What to show:** What formalization *reveals* about frameworks they already know. The compiler as a new lens on familiar material. Don't teach Lean syntax — show what the compiler *said*.

**What resonates:**
- Bunge's "asymmetric" error caught after 47 years in print
- The commuting triangle proving Bunge and Mobus are compatible despite never citing each other
- Mobus's N/G as the natural structure family (they'll recognize this immediately)
- The Joslyn feedback loop: advisor question → proof assistant → new findings

---

## What to Skip

- **Finding 8 details** (three subsystem orderings): Too much for a talk. Save for Q&A if someone asks about subsystem ordering in the family representation.
- **KlirSystem ext fix**: Too inside-baseball. Only mention in the journal paper as a methodology anecdote.
- **Lean syntax details**: Show signatures, don't explain tactic proofs.
- **BRA companion project**: Mention briefly for operational grounding, don't go deep.

---

## Suggested Talk Structure

1. **Opening: Klir as common root** — The `S = (T, R)` that started everything. Klir (1969/2001) provides the mathematical common ancestor. Both Bunge and Mobus cite Klir independently. Neither cites the other.

2. **The commuting triangle** — Three frameworks, one verified diagram. Mobus → Bunge → Klir = Mobus → Klir. The `rfl` proof: definitionally identical, not merely equivalent.

3. **What the compiler found** — Bunge's "asymmetric" error. Cross-volume dependencies. Under-specification revealed. Things decades of reading didn't catch.

4. **A1: The advisor's question** — Cliff asks: "S is a set of sets of tuples, right?" This is the centerpiece slide.

5. **Finding 3: The answer** — Flattening commutes. Both readings are equivalent for the proved theorems. The flat encoding is a faithful quotient, certified by the compiler.

6. **Finding 6: The surprise** — Mobus's N/G IS the natural structure family. The bridge theorem was already performing the flattening. A relationship between the two frameworks, hidden in plain sight until formalization made it visible.

7. **Methodology** — LLM-assisted formalization: human steers, AI writes Lean, compiler verifies. Low marginal cost makes formal verification accessible to domain experts.

8. **Operational pipeline** — Three layers, each serving a distinct function:
   - Lean 4 validates the mathematical foundations (are the frameworks compatible?).
   - Onto-viz tracks implementation coverage (which Mobus concepts has BERT implemented?).
   - BERT renders the 8-tuple as interactive models practitioners can build and explore.
   - The formalized ontology isn't purely theoretical — it grounds working software.

9. **Philosophical punchline** — The standard view: you know what to prove, and the tool checks it. That's not what happened. The `rfl` was *discovered*, not anticipated. The error was *found*, not sought. The proof assistant was not a verification tool but an *instrument of inquiry*. It forced precision that revealed structure nobody had seen, including the original authors.

10. **Close** — The intellectual lineage: Klir → Joslyn → the author, who built BERT on Mobus and formalized Bunge. The commuting triangle is the formal structure of this tradition made visible.

---

## Key Theorem References

| Slide | Theorem | Source |
|-------|---------|--------|
| Commuting triangle | `triangle_commutes` | KlirSystem.lean |
| A1 answer | `flatten_internal_commutes` | StructureFamily.lean:135 |
| A1 answer (ext) | `flatten_external_commutes` | StructureFamily.lean:150 |
| Finding 6 | `MobusSystem.toRichBunge_flatten_eq` | StructureFamily.lean:430 |
| Extended diagram | `rich_triangle_commutes` | StructureFamily.lean:281 |
