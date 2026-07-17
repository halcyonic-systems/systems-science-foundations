# System-Type Typologies

*Author-grounded vocabulary for the kind of a system: kingdoms, genera, and the domain axis.*

**Purpose**: Curated reference for the system-type property a modeler asserts on a model (bert-lenses issue #71). It answers one question — *what vocabulary do the founding authors give us for saying "this is a social system" or "a technical system"?* — and grounds each term in its source. The canonical assertion vocabulary bert-lenses ships is **Bunge's five genera** (Physical, Chemical, Biological, Social, Technical) under his two kingdoms (Conceptual, Concrete). This doc records why, and how Mobus and Klir line up with it.

---

## 1. Bunge — kingdoms and genera

Bunge's *Treatise on Basic Philosophy*, Vol. 4 (*Ontology II: A World of Systems*, 1979) fixes the type axis in two layers.

### Kingdoms (Conceptual | Concrete)

> "A system, then, is a complex object, the components of which are interrelated rather than loose. If the components are conceptual, so is the system; if they are concrete or material, then they constitute a concrete or material system. A theory is a conceptual system, a school a concrete system of the social kind. **These are the only system kingdoms we recognize: conceptual and concrete.** We have no use for mixed systems…" (§1.2, ~p. 6)

So the top split is exhaustive and exclusive: every system is either **Conceptual** or **Concrete**. Genus applies within the Concrete kingdom.

### Genera (five concrete kinds)

Bunge's §6.2 "System Genera" enumerates the kinds current science accepts, then compresses them into a postulate:

> **Postulate 6.4** At the present stage of the evolution of the universe there are five system genera: **physical, chemical, biological, social, and technical.** I.e. the family of system genera is 𝒮 = {S₁, S₂, S₃, S₄, S₅}.

| Genus | Bunge's gloss (§6.2) | Examples |
|-------|----------------------|----------|
| **Physical** | microphysical → megaphysical | atoms, fields, bodies, galaxies |
| **Chemical** | not lumped with physical (chemosystems are never at rest, respond quickly, use catalyzers) | chemical reactors, compost piles |
| **Biological** | microbiological → megabiological | single cells, organisms, ecosystems |
| **Social** | microsocial → megasocial | families, villages, cities, nations |
| **Technical** | artifacts — set apart by human work, intelligence, purposiveness | this book, farms, industrial plants |

Bunge's remarks on why the list is exactly five are worth keeping: physical vs chemical are split on dynamical grounds; **psychosystems** are folded into biological ("fear of encouraging the myth of disembodied minds"); **technical** systems are kept separate because artifacts "bear the stamp of human intelligence and purposiveness." The "present stage" clause is deliberate — Bunge allows that further genera could emerge (or be wiped out).

**Sources**: prose in `operations/systems-science/bunge/Bunge - 1979 - Treatise on Basic Philosophy.md` — kingdoms at §1.2 (line ~328), the natural/artificial framing at line ~298, genera at §6.2 (line ~3989), Postulate 6.4 in the same section. (The earlier spec pointer to an `archive/experiments/.../QTHMLVUZ.md` §6.2 extract is stale — the file is gone; cite the prose above.)

---

## 2. Mobus — concrete vs abstract, plus texture axes

Mobus (*Systems Science: Theory, Analysis, Modeling, and Design*) aligns with Bunge's kingdoms and adds orthogonal "texture" axes that describe a system rather than sort it into a genus.

### Concrete vs abstract (≈ Bunge's kingdoms)

> "It will be important to differentiate between **concrete or real physical systems** and **abstract systems**… Examples of concrete systems include animals, organizations, nations, and the whole Earth. Abstract systems are conceptual… and come in two flavors. **Pure abstract systems** are those, like the natural or real numbers… The second form of abstract system is what we generally call a **'model.'**" (§1.1.3, `operations/systems-science/mobus/1-Introduction.md`, ~lines 89–98)

Mobus's *concrete* = Bunge's *concrete* kingdom; Mobus's *abstract/conceptual* = Bunge's *conceptual* kingdom, refined into two flavors (pure-abstract, e.g. the reals; and models). Mobus's project is the bridge between the concrete and the model, via pure-abstract constructs.

### Texture axes (not genera)

Beyond the kingdom split, Mobus (via Miller, Ackoff, Checkland) tags a system along descriptive axes that cut across genus:

- **crisp ↔ fuzzy** — how sharply the boundary/state is defined.
- **hard ↔ soft** (Checkland) — engineered/well-defined vs human-activity/ill-defined.
- **closed ↔ open** — isolation vs exchange with an environment.
- **simple → complex → complex adaptive (CAS) → complex adaptive & evolvable (CAES)** — an organizational-complexity ladder.

These are properties of a system, not a partition of the type space, so they are **not** part of the asserted-genus vocabulary; they are candidate future metadata axes if the field earns them.

---

## 3. Klir — §2.4 Classification of Systems (a genus typology after all)

Klir (*Facets of Systems Science*) §2.4 "Classification of Systems" gives a two-axis classification of the ordered pair S = (T, R):

> "This can be done in one of two fundamentally different ways:
> **a.** By restricting T to certain kinds of things;
> **b.** By restricting R to certain kinds of relations."
> (`operations/systems-science/klir/klir-facets.md`, §2.4, ~lines 1625–1658)

- **Type (a) — restrict the things (T):** "exemplified by the traditional classification of science into disciplines… each focusing on the study of certain kinds of things (**physical, chemical, biological, economic, social, etc.**) without committing to any particular kind of relations." Experimentally based.
- **Type (b) — restrict the relations (R):** "fundamentally different classes of systems, each characterized by special kinds of relations, with no commitment to any particular kind of things." Theoretically based, and "fundamental to systems science."

Klir also defines the **general system** as the interpretation-free canonical representative of an isomorphic equivalence class (~lines 1763–1765): "a general system is a standard and interpretation-free system chosen to represent a particular equivalence class of isomorphic systems." That is Klir's systemhood axis (type-b territory), distinct from the thinghood classification of type (a).

**Not to be confused** with Klir's *epistemological hierarchy* — source → data → generative → structure → metasystem — which is a hierarchy of knowledge *levels* about a system, not a genus typology. §2.4 is the type axis; the epistemic levels are a separate concern.

---

## 4. Convergence — Bunge's genera ≅ Klir's type-(a) axis

Bunge's five genera and Klir's §2.4 type-(a) list land on nearly the same partition, reached independently:

| Bunge (Postulate 6.4) | Klir §2.4 type-(a) |
|-----------------------|--------------------|
| Physical | physical |
| Chemical | chemical |
| Biological | biological |
| Social | economic, social |
| Technical | (— disciplinary list is open-ended: "etc.") |

Two authors, from different starting points (Bunge from scientific ontology, Klir from the observer-relative pair S = (T, R)), converge on **physical / chemical / biological / social…** as the natural partition of *things*. This is an independent corroboration of the **K≅2** thesis this repository is built on: the common core of systems science latches the same invariant across traditions. The convergence is on the *thinghood* (type-a / genus) axis; the deeper systems-science content, for both authors, lives on the *systemhood* (relation) axis — Klir's type (b) and general systems, Bunge's structure/mechanism.

---

## 5. What bert-lenses ships

- **Kingdom**: `Conceptual | Concrete` (Bunge §1.2).
- **Genus**: `Physical | Chemical | Biological | Social | Technical` (Bunge Postulate 6.4), meaningful when kingdom = Concrete.
- **Domain**: free-text subject area (e.g. "U.S. legislative process") — the narration context, not an ontological kind.

The genus vocabulary is Bunge's, chosen because it is a closed, postulated list (exactly five) that Klir's type-(a) axis independently corroborates. Mobus's texture axes and Klir's type-(b)/general-system axis are deliberately *not* encoded as genus — they describe or theoretically reclassify a system, they do not name its kind. The property is asserted metadata, never a systemhood verdict; no validator gates it.
