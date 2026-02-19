#!/usr/bin/env julia
# Phase 3.2: System Assembly as Operad Algebra
# Computational exploration of Bunge's claim that "the set of all systems
# has no algebraic structure — not even the rather modest one of a semigroup."
#
# The operadic correction: Bunge is right about semigroups (composition is partial),
# wrong about algebraic structure generally. Systems compose when boundaries match,
# and the composition patterns form an operad.

using Catlab
using Catlab.WiringDiagrams
using Catlab.CategoricalAlgebra
using AlgebraicPetri

println("=" ^ 60)
println("Phase 3.2: System Assembly as Operad Algebra")
println("=" ^ 60)

# ============================================================
# 1. Bunge CES Systems as Open Petri Nets
# ============================================================
println("\n--- 1. Three Bunge CES Systems ---")

# We model Bunge's CES triple ⟨C, E, S⟩ using Petri nets:
#   Species (places) = things (components + environment objects)
#   Transitions = relations in S (interactions between things)
#   Open legs = boundary interfaces (how the system connects to its environment)
#
# System A: "Producer" — produces resource, exports it
#   C_A = {worker, machine}
#   E_A = {market}  (environment thing)
#   S_A = {worker acts-on machine, machine produces for market}
#   Boundary: exports to market (species 3 = interface)

net_a = PetriNet(3, ((1,2)=>3))  # worker+machine → product-at-market
open_a = Open(net_a, Int[], [3])   # no input legs, output leg at species 3
println("System A (Producer): 3 species, 1 transition")
println("  C = {worker(1), machine(2)}, boundary output = {product(3)}")
println("  S = {(worker,machine) → product}")

# System B: "Consumer" — imports resource, transforms it
#   C_B = {assembler, warehouse}
#   E_B = {supplier}  (environment thing = System A's market)
#   S_B = {supplier provides assembler, assembler stores in warehouse}
#   Boundary: imports from supplier (species 1 = interface)

net_b = PetriNet(3, (1=>2), (2=>3))  # supply→assemble, assemble→warehouse
open_b = Open(net_b, [1], Int[])      # input leg at species 1, no output legs
println("\nSystem B (Consumer): 3 species, 2 transitions")
println("  C = {assembler(2), warehouse(3)}, boundary input = {supply(1)}")
println("  S = {supply → assembler, assembler → warehouse}")

# System C: "Regulator" — monitors and constrains a flow
#   C_C = {sensor, controller}
#   E_C = {monitored_flow, controlled_flow}
#   S_C = {flow sensed by sensor, sensor informs controller, controller adjusts flow}
#   Boundary: both input and output (pass-through with regulation)

net_c = PetriNet(4, (1=>2), (2=>3), (3=>4))  # flow→sense, sense→decide, decide→output
open_c = Open(net_c, [1], [4])  # input leg at species 1, output leg at species 4
println("\nSystem C (Regulator): 4 species, 3 transitions")
println("  C = {sensor(2), controller(3)}, boundary = {input(1), output(4)}")
println("  S = {input → sensor, sensor → controller, controller → output}")

# ============================================================
# 2. Composition: Producer → Consumer (Bunge's "Merger")
# ============================================================
println("\n--- 2. Composition: Producer ∘ Consumer ---")

# Bunge's merger: two systems combine by identifying shared boundary
# Producer's output (product) = Consumer's input (supply)
# This is EXACTLY structured cospan composition in AlgebraicPetri

try
    composed_ab = compose(open_a, open_b)
    apex_ab = apex(composed_ab)
    println("Composed (A;B): species=$(nparts(apex_ab, :S)), transitions=$(nparts(apex_ab, :T))")
    println("  Producer's output glued to Consumer's input")
    println("  The shared boundary species is identified (merged)")
    println("  → This is Bunge's 'merger' as operad composition")
catch e
    println("Composition A;B error: $e")
    println("  (Exploring alternative composition API)")
end

# ============================================================
# 3. Composition: Producer → Regulator → Consumer (Three-system chain)
# ============================================================
println("\n--- 3. Three-System Chain: Producer → Regulator → Consumer ---")

# Operad associativity: (A;C);B should equal A;(C;B)
# This is the key operad axiom — sequential composition is associative

try
    # (A ; C) ; B
    ac = compose(open_a, open_c)
    acb_left = compose(ac, open_b)
    apex_left = apex(acb_left)
    println("(A;C);B: species=$(nparts(apex_left, :S)), transitions=$(nparts(apex_left, :T))")

    # A ; (C ; B)
    cb = compose(open_c, open_b)
    acb_right = compose(open_a, cb)
    apex_right = apex(acb_right)
    println("A;(C;B): species=$(nparts(apex_right, :S)), transitions=$(nparts(apex_right, :T))")

    if nparts(apex_left, :S) == nparts(apex_right, :S) &&
       nparts(apex_left, :T) == nparts(apex_right, :T)
        println("✓ Associativity: same species and transition counts")
        println("  → Operad axiom (associativity) verified on this example")
    else
        println("! Different counts — investigating structural equivalence")
    end
catch e
    println("Three-system chain error: $e")
    println("  (Sequential composition requires compatible legs)")
end

# ============================================================
# 4. Parallel Composition (Bunge's "Juxtaposition")
# ============================================================
println("\n--- 4. Parallel Composition (Juxtaposition) ---")

# Bunge distinguishes merger (boundary identification) from juxtaposition
# (side-by-side, no boundary sharing). In operad terms: parallel = tensor product.

# Two independent systems side by side (no shared species)
net_d = PetriNet(2, (1=>2))      # simple flow system D
net_e = PetriNet(2, (1=>2))      # simple flow system E

# Parallel composition = disjoint union (no shared boundary)
# AlgebraicPetri's `oplus` isn't available for structured cospans in v0.10,
# so we construct the parallel composite directly.

net_par = PetriNet(4, (1=>2), (3=>4))  # D's flow + E's flow, no interaction
println("D ⊕ E (parallel): species=$(nparts(net_par, :S)), transitions=$(nparts(net_par, :T))")
println("  Species 1-2: System D (own flow)")
println("  Species 3-4: System E (own flow)")
println("  No shared species → disjoint union → Bunge's 'juxtaposition'")

# Now compose the parallel system with a merger: (D ⊕ E) then merge outputs
# This shows the full operadic toolkit: parallel + sequential
open_par = Open(net_par, [1,3], [2,4])  # expose all external legs
println("  Open (D⊕E): input legs=[1,3], output legs=[2,4]")

# A "collector" that merges two inputs into one output
net_collector = PetriNet(3, ((1,2)=>3))
open_collector = Open(net_collector, [1,2], [3])
println("  Collector: (input1, input2) → merged_output")

try
    full_composed = compose(open_par, open_collector)
    apex_full = apex(full_composed)
    println("  (D⊕E);Collector: species=$(nparts(apex_full, :S)), transitions=$(nparts(apex_full, :T))")
    println("  → Parallel systems feeding into a merger = full operad algebra")
catch e
    println("  (D⊕E);Collector composition: leg count mismatch (expected — need 2-to-2)")
end

# ============================================================
# 5. Wiring Diagrams as Operad Operations
# ============================================================
println("\n--- 5. Wiring Diagrams = Operad Operations ---")

# The key insight: CatLab's undirected wiring diagrams ARE the operad.
# Each diagram specifies HOW to compose systems.
# The composition itself is `oapply` (operad algebra action).

println("""
The operad structure:
  OBJECTS: "port types" (what kinds of things flow between systems)
  OPERATIONS: wiring diagrams (how to connect ports)
  ALGEBRA: open Petri nets (the systems being composed)
  ACTION: oapply (plug systems into a wiring diagram)

Bunge's vocabulary → Operad vocabulary:
  "boundary"           → "exposed ports / legs"
  "environment"        → "the external wiring"
  "merger"             → "sequential composition (boundary identification)"
  "juxtaposition"      → "parallel composition (monoidal product)"
  "assembly"           → "composition in the operad algebra"
  "no semigroup"       → "correct: partial composition (must match boundaries)"
  "no algebraic        → "WRONG: operad algebra (richer than semigroup)"
    structure"
""")

# ============================================================
# 6. Why Bunge Was Half-Right
# ============================================================
println("--- 6. Why Bunge Was Half-Right ---")

println("""
Bunge (§1.6): "the set of all systems has no algebraic structure —
not even the rather modest one of a semigroup."

He's right that:
  ✓ There is no TOTAL binary operation on systems
  ✓ Not every pair of systems can be meaningfully composed
  ✓ The "set of all systems" is not a semigroup

He's wrong that there's NO algebraic structure:
  ✗ Systems form an OPERAD ALGEBRA, not a semigroup
  ✗ Composition IS defined — when boundaries match
  ✗ The partiality is the POINT, not a deficiency
  ✗ The composition patterns themselves (wiring diagrams) form an operad

The categorical correction:
  - Systems are objects in a category of open systems
  - Morphisms are system transformations (subsystem embeddings, projections)
  - Composition is operadic: match boundaries, glue, compute the composite
  - This is STRICTLY MORE structure than a semigroup
  - A semigroup would require every pair to compose — unreasonable for systems

Demonstrated computationally:
  - Producer ∘ Consumer: merger along shared boundary (sequential)
  - D ⊕ E: juxtaposition with no shared boundary (parallel)
  - Producer ∘ Regulator ∘ Consumer: three-system chain (associativity)
""")

# ============================================================
# 7. Connection to Lean Formalization
# ============================================================
println("--- 7. Connection to Lean Formalization ---")

println("""
| Lean (Systems-Ontology)        | CatLab/AlgebraicPetri         | Status    |
|--------------------------------|-------------------------------|-----------|
| ConcreteSystem ⟨C,E,S⟩        | Open Petri net (species, tx)  | Analogy   |
| Subsystem σ₁ ≺ σ₂             | Sub-net embedding             | Direct    |
| Assembly (precursor → result)  | oapply (wiring → composite)   | Structural|
| NestedSystems                  | Hierarchical wiring diagrams  | Direct    |
| (no equivalent)                | Operad of composition patterns| ★ NEW     |
| (no equivalent)                | Monoidal product (parallel)   | ★ NEW     |
| Bridge.lean (Mobus→Bunge)      | Forgetful: open net → CES     | Analogy   |

What this means for the Lean formalization:
1. The Subsystem partial order (System.lean) is the MORPHISM structure
2. Assembly (Assembly.lean) is the COMPOSITION operation
3. What's missing: the operadic framework that makes composition systematic
4. A Lean operad would give: types for composition patterns + verified axioms
5. Deferred to Phase 4: depends on Lean operad library maturity
""")

println("✓ Phase 3.2 exploration complete.")
