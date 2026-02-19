#!/usr/bin/env julia
# CatLab.jl Visualizations for Categorification Phases 1 & 2
# Generates Graphviz DOT output for the categorical structures

using Catlab
using Catlab.Theories
using Catlab.CategoricalAlgebra
using Catlab.WiringDiagrams
using Catlab.Graphics

# ============================================================
# 2a. Ordering Triangle — Three Preorder Categories on Fin 2
# ============================================================
# We demonstrate the ordering triangle on a concrete 3-system example
# where the non-fullness witnesses are visible.

println("=" ^ 60)
println("2a. Ordering Triangle on Concrete Examples")
println("=" ^ 60)

# Define three preorders using FinCat (finite category) presentations
# Systems: A (small/merged), B (large/split), C (medium)

# FlatOrd: subsystem by aggregate structure inclusion
# A ≤_flat B, A ≤_flat C (A's flat structure ⊆ B's and C's)
flat_graph = @acset Graph begin
    V = 3  # A=1, B=2, C=3
    E = 5  # reflexive + A≤B, A≤C
    src = [1, 2, 3, 1, 1]
    tgt = [1, 2, 3, 2, 3]
end
println("\nFlat ordering (5 morphisms on 3 objects):")
println("  A → A, B → B, C → C (reflexive)")
println("  A → B, A → C (A is flat-subsystem of B and C)")

# RefinementOrd: subsystem by refinement (each family member ⊆ some target member)
# A ≤_ref B (still holds), but A ≤_ref C may fail
ref_graph = @acset Graph begin
    V = 3
    E = 4  # reflexive + A≤B only
    src = [1, 2, 3, 1]
    tgt = [1, 2, 3, 2]
end
println("\nRefinement ordering (4 morphisms on 3 objects):")
println("  A → A, B → B, C → C (reflexive)")
println("  A → B (A is refinement-subsystem of B)")
println("  A → C is MISSING — non-fullness witness for forgetRefinement")

# FamilyOrd: subsystem by exact family membership
# Only reflexive (strictest ordering)
fam_graph = @acset Graph begin
    V = 3
    E = 3  # reflexive only
    src = [1, 2, 3]
    tgt = [1, 2, 3]
end
println("\nFamily ordering (3 morphisms on 3 objects):")
println("  A → A, B → B, C → C (reflexive only)")
println("  A → B is MISSING — non-fullness witness for forgetFamily")

println("\n→ forgetFamily: FamilyOrd → RefinementOrd")
println("  Faithful: 3 morphisms → 3 morphisms (injective)")
println("  NOT Full: RefinementOrd has A→B but FamilyOrd doesn't")
println("\n→ forgetRefinement: RefinementOrd → FlatOrd")
println("  Faithful: 4 morphisms → 4 morphisms (injective)")
println("  NOT Full: FlatOrd has A→C but RefinementOrd doesn't")

# ============================================================
# 2b. Bridge Factorization — Functor Composition
# ============================================================
println("\n" * "=" ^ 60)
println("2b. Bridge Factorization")
println("=" ^ 60)

# Model as a wiring diagram: Mobus system with N (internal) and G (external)
# Using CatLab's wiring diagram infrastructure

# Define a simple Mobus system as a box with boundary ports
println("\nModeling Mobus system as wiring diagram box:")
println("  Input ports (external inflows via G)")
println("  Output ports (external outflows via G)")
println("  Internal wiring (N)")

# Create a simple wiring diagram showing the factorization
d = WiringDiagram([:MobusIn], [:BungeOut])

# Mobus → Rich (preserves {N, G} as family)
toRich = add_box!(d, Box(:toRichBunge, [:MobusIn], [:RichOut]))
# Rich → Flat (flattens family to single relation)
flatten = add_box!(d, Box(:flatten, [:RichIn], [:BungeOut]))

# Wire: input → toRichBunge → flatten → output
add_wire!(d, (input_id(d), 1) => (toRich, 1))
add_wire!(d, (toRich, 1) => (flatten, 1))
add_wire!(d, (flatten, 1) => (output_id(d), 1))

println("  Wiring diagram created: MobusIn → toRichBunge → flatten → BungeOut")
println("  This IS toBunge = toRichBunge ⋙ flatten")

# Try to generate Graphviz output
try
    graphviz_str = sprint(show, MIME"text/plain"(), to_graphviz(d))
    println("\n  Graphviz representation generated ($(length(graphviz_str)) chars)")
catch e
    println("\n  Note: Graphviz rendering requires additional setup: $e")
end

# ============================================================
# 2c. Collapse Functor — Non-Faithfulness Witness
# ============================================================
println("\n" * "=" ^ 60)
println("2c. Collapse Functor — Non-Faithfulness Witness")
println("=" ^ 60)

# BtcState category: objects are UTXO sets, morphisms are transaction traces
# We model a small example directly

# Objects
println("\nBtcState objects (small example):")
println("  bs = {⟨val=3, addr=0⟩, ⟨val=7, addr=0⟩}")
println("  totalValue(bs) = 10")

# Two distinct endomorphisms on bs
println("\nTwo distinct endomorphisms bs → bs:")
println("  f₁ = [tx₁] where tx₁ = (consume {u3}, produce {u3})")
println("  f₂ = [tx₂] where tx₂ = (consume {u7}, produce {u7})")
println("  f₁ ≠ f₂ because [tx₁] ≠ [tx₂]")

# Collapse
println("\nAfter collapse:")
println("  collapse(bs) = {addr0 ↦ 10}")
println("  collapseFunctor.map f₁ = id_{collapse(bs)}  (unique in thin Eth)")
println("  collapseFunctor.map f₂ = id_{collapse(bs)}  (same!)")
println("  → map is NOT injective → ¬ Faithful")

# Model the Btc category with a finite presentation
# 1 object, 3 morphisms: id, f₁, f₂
println("\nBtcState (restricted to bs) as a finite category:")
println("  Objects: {bs}")
println("  Hom(bs, bs) = {id=[], f₁=[tx₁], f₂=[tx₂], f₁∘f₂=[tx₁,tx₂], ...}")
println("  (infinite hom-set from arbitrary-length traces)")

println("\nEthState (restricted to collapse(bs)) as thin category:")
println("  Objects: {e = addr0↦10}")
println("  Hom(e, e) = {id}  (exactly one — thin)")

# ============================================================
# 2d. Full Project Map — Summary Statistics
# ============================================================
println("\n" * "=" ^ 60)
println("2d. Full Project Functor Map — Summary")
println("=" ^ 60)

println("""
┌───────────────────────────────────────────────────┐
│     SYSTEMS ONTOLOGY (Phase 1) — ~2,930 lines     │
│                                                   │
│  MobusSys ──toRichBunge──→ RichSys ──flatten──→ BungeSys──→ KlirSys
│                                                   │
│  FamilyOrd ──forget──→ RefinementOrd ──forget──→ FlatOrd
│       (Faithful, ¬Full)     (Faithful, ¬Full)     │
└───────────────────────────────────────────────────┘

┌───────────────────────────────────────────────────┐
│     BRA / CRYPTO (Phase 2) — 1,080 lines          │
│                                                   │
│  BtcState ──collapseFunctor──→ EthState           │
│     (non-thin)  (EssSurj, ¬Faithful)  (thin)     │
│     totalValue ────────────── totalValue           │
│                (commutes)                          │
└───────────────────────────────────────────────────┘

Shared pattern: thin preorder categories via Preorder.smallCategory
Combined: ~4,010 lines, 31 files, zero sorry's
""")

# ============================================================
# Graphviz DOT output for the full functor map
# ============================================================
println("=" ^ 60)
println("Graphviz DOT output (paste into graphviz/dot renderer)")
println("=" ^ 60)

dot_output = """
digraph CategorificationMap {
    rankdir=TB;
    fontname="Helvetica";
    node [fontname="Helvetica", shape=box, style="rounded,filled"];
    edge [fontname="Helvetica", fontsize=10];

    subgraph cluster_phase1 {
        label="Systems Ontology — Phase 1\\n~2,930 lines, 20 modules, 0 sorry";
        style=filled; fillcolor="#f5f5f5"; color="#1565c0";
        fontsize=12; fontcolor="#1565c0";

        MobusSys [label="MobusSys\\n⟨C,N,E,G,B,T,H,Δt⟩", fillcolor="#fce4ec"];
        RichSys [label="RichSys\\n{N.toRelation, G.toRelation}", fillcolor="#e8f5e9"];
        BungeSys [label="BungeSys\\n⟨C, E, ⋃₀{N,G}⟩", fillcolor="#e3f2fd"];
        KlirSys [label="KlirSys\\n(T, R)", fillcolor="#fff3e0"];

        MobusSys -> RichSys [label="toRichBunge"];
        RichSys -> BungeSys [label="flattenFunctor"];
        BungeSys -> KlirSys [label="toKlir"];
        MobusSys -> BungeSys [label="toBunge = ⋙", style=dashed, color="#888"];

        FamilyOrd [label="FamilyOrd", fillcolor="#e3f2fd"];
        RefinementOrd [label="RefinementOrd", fillcolor="#e8f5e9"];
        FlatOrd [label="FlatOrd", fillcolor="#fff3e0"];

        FamilyOrd -> RefinementOrd [label="forgetFamily\\nFaithful, ¬Full"];
        RefinementOrd -> FlatOrd [label="forgetRefinement\\nFaithful, ¬Full"];
    }

    subgraph cluster_phase2 {
        label="BRA / Crypto — Phase 2\\n1,080 lines, 11 files, 0 sorry";
        style=filled; fillcolor="#f5f5f5"; color="#c62828";
        fontsize=12; fontcolor="#c62828";

        BtcState [label="BtcState\\n(non-thin, List Transaction)", fillcolor="#fff3e0"];
        EthState [label="EthState\\n(thin, totalValue ordering)", fillcolor="#e3f2fd"];
        NatVal [label="ℕ\\ntotalValue", fillcolor="#f3e5f5"];

        BtcState -> EthState [label="collapseFunctor\\nEssSurj, ¬Faithful"];
        BtcState -> NatVal [label="totalValue", style=dashed];
        EthState -> NatVal [label="totalValue", style=dashed];
    }
}
"""

println(dot_output)

# Write DOT to file
dot_path = joinpath(dirname(@__DIR__), "docs", "categorical-map.dot")
open(dot_path, "w") do f
    write(f, dot_output)
end
println("DOT file written to: $dot_path")

# Try to render SVG
try
    svg_path = replace(dot_path, ".dot" => ".svg")
    run(`dot -Tsvg -o $svg_path $dot_path`)
    println("SVG rendered to: $svg_path")
catch e
    println("Note: SVG rendering requires graphviz 'dot' command: $e")
end

println("\n✓ All diagram generation complete.")
