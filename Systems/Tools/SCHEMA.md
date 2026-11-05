# `decls.json`: the dump schema, version 1.0

`lake exe dump` (`Systems/Tools/Dump.lean`) writes the development as one JSON
object. This page documents every field, the rule that decides what is a node,
and what a reader may rely on across versions. The reader today is the atlas
at math.systems (repo `mathematical-systems`), pinned to one SSF commit by its
`atlas/lean-pin`; CI publishes the file for each commit on `main` as a GitHub
Release asset,
`https://github.com/halcyonic-systems/systems-science-foundations/releases/download/dump-<sha>/decls.json`
(`.github/workflows/dump.yml`).

## Top level

| Field | Type | Meaning |
|---|---|---|
| `schema` | string | This document's version, `"MAJOR.MINOR"`. Check it first. |
| `project` | string | Always `"systems-science-foundations"`. |
| `commit` | string | Full SHA of `HEAD` in the checkout the dump ran in. |
| `generatedAt` | string | UTC timestamp, `YYYY-MM-DDTHH:MM:SSZ`. |
| `toolchain` | string | Contents of `lean-toolchain`, e.g. `leanprover/lean4:v4.28.0`. |
| `modules` | array | One object per owned module that has at least one node (below). Sorted by `name`. |
| `declarations` | array | One object per node. Sorted by module name, then by `line`. |

## `modules[]`

| Field | Type | Meaning |
|---|---|---|
| `name` | string | Module name, e.g. `Systems.Category.ShapeKlir`. |
| `file` | string | Path from the repo root, `Systems/Category/ShapeKlir.lean`. |
| `declarations` | number | Count of nodes in this module. |
| `doc` | string | The module docstrings (`/-! ... -/`), joined by a blank line. `""` when there are none. |

## `declarations[]`

| Field | Type | Meaning |
|---|---|---|
| `name` | string | Fully qualified constant name. Unique across the file. |
| `kind` | string | One of `structure`, `class`, `theorem`, `axiom`, `inductive`, `opaque`, `instance`, `field`, `def`, `other`. A `def` whose type is a `Prop` is reported as `theorem`; a structure projection as `field`. |
| `module` | string | The module that declares it; always a `modules[].name`. |
| `line` | number | First line of the declaration's source range, 1-based, inclusive. |
| `endLine` | number | Last line of the source range, 1-based, inclusive. |
| `doc` | string or null | The docstring, or `null` when there is none (or `--no-doc`). |
| `signature` | string | The pretty-printed signature, width 100, app unexpanders applied. Falls back to the name alone when printing fails (or `--no-signature`). |
| `uses` | array of string | Names of nodes this declaration uses, contracted through generated constants (rule below). Sorted. Every entry is a `declarations[].name` in this same file; no edge dangles. |
| `axioms` | array of string | Axioms the proof rests on, as `#print axioms` would list them (`propext`, `Classical.choice`, `Quot.sound`; any other name is a finding). Sorted. Empty with `--no-axioms`. |
| `atlas` | array of string | Atlas entry ids this declaration formalises, from `@[atlas "entry-id"]` (`Systems/Tools/Atlas.lean`). Usually empty; one or two ids when present. |
| `source` | string | The source text, lines `line` to `endLine` of `module`'s file, newline-joined, verbatim. |
| `constructors` | array | For `kind` in `inductive`, `structure`, `class`: the constructors (one for a structure or class, zero for an empty inductive). Empty for every other kind. |

## `constructors[]`

| Field | Type | Meaning |
|---|---|---|
| `name` | string | Fully qualified constructor name, e.g. `KlirArrow.relation`. Constructors are not nodes. |
| `doc` | string or null | The constructor's docstring, or `null`. |
| `type` | string | Its pretty-printed type, width 100; `""` when printing fails. |
| `args` | array of string | The constant arguments of the result type, after all binders: `KlirArrow .relation .things` gives `["KlirPosition.relation", "KlirPosition.things"]`. Lets a quiver be read without parsing `type`. |

## The node rule

A constant is a node, and so a `declarations[]` entry, when all of these hold:

1. Its module is owned: under the `Systems` root and not under `Systems.Tools` (the dump and the atlas attribute are not part of the development).
2. It is not private and not an internal detail (`Name.isInternalDetail`).
3. It is not a constructor, a recursor or a quotient primitive, and not an auxiliary the elaborator generated: `rec`, `recOn`, `casesOn`, `below`, `brecOn`, `noConfusion`, `inj`, `injEq`, `sizeOf_spec`, `ofNat`, `toCtorIdx`, `eq_1`, `eq_def` and kin, or any name component starting with `match_`, `proof_`, `eq_` or `_`. The full list is `generatedSuffixes` in `Dump.lean`.
4. It has a source range. Nothing the elaborator generated has one, so this also catches what the list misses.

**Contraction.** `uses` is computed from the constants in the declaration's type and value. A used constant that is owned but not a node (a `match_` helper, an equation lemma, a recursor) is replaced by what it in turn uses, transitively, until only nodes remain. The graph is therefore drawn on the declarations a reader can name, as the Stacks project does with untagged helper paths.

**Mathlib is a leaf.** Constants from Mathlib, Lean core, Batteries or any other dependency are never nodes and never appear in `uses`. A declaration that only uses Mathlib has `uses: []`. Nothing in the file says which Mathlib constants were used.

**Ordering.** `declarations` is sorted by module name, then by `line`; `modules` by name. The sort is stable across runs on the same commit. `generatedAt` is the only field that differs between two runs on the same commit and toolchain.

## Stability promise

- The `schema` field is `"MAJOR.MINOR"`.
- An additive change bumps the **minor**: a new field anywhere, a new `kind` value, a new entry in `generatedSuffixes` that only removes constants nobody could name. A reader that ignores unknown fields keeps working.
- A removal or rename of a field, a change to a field's type or meaning, a change to the node rule that adds or removes nodes a reader may have linked to, or a change to the ordering guarantee bumps the **major**.
- A reader checks `schema` and refuses a major it does not know. It pins the SSF commit, so a new major only reaches it when the pin moves.
- This document and the `schema` literal in `Dump.lean` change in the same commit.

## History

| Version | Commit | Change |
|---|---|---|
| 1.0 | this file's first commit | First versioned schema: the fields above, as the dump wrote them on 2026-11-05 (1630 declarations in 84 modules). |
