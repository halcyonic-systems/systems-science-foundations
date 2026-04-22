# Verso Interactive Documents

Interactive documents built with [Verso](https://github.com/leanprover/verso), rendering live Lean 4 code alongside typeset mathematics and English prose.

## Documents

- **SystemsProposal** — "A Formal Systems Ontology and Its Open Frontier" (6 chapters, live Lean hovers)
- **BuildingStory** — "Building Story" (development narrative, prose only)

## Building

Requires Lean 4 v4.28.0 (set by `lean-toolchain`).

```bash
lake exe proposal        # build the flagship document
lake exe building-story  # build the companion narrative
./build.sh               # build both with Halcyonic theme
```

Output goes to `_out/html-multi/`. Serve via HTTP to get working hovers and search:

```bash
cd _out/html-multi && python3 -m http.server 8080
```
