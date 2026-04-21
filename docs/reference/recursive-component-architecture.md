# RecursiveComponent Architecture: Connecting Phase 1 to Phase 2

*How the existing `RecursiveComponent` in Level.lean (Mobus Eq. 4.3) connects to the planned `MobusSystem` structure, including the atomic work process taxonomy and the mutual recursion design challenge.*

**Project**: Systems Ontology — Lean 4 Formalization
**Scope**: Bridge from Phase 1 (Bunge core) to Phase 2 (Mobus 8-tuple)
**Date**: 2026-02-17

---

## 1. What RecursiveComponent Currently Captures

Phase 1 includes a `RecursiveComponent` inductive type in Level.lean (lines 53–58) that formalizes the two-case distinction from Mobus Eq. 4.3:

```
inductive RecursiveComponent (α : Type*) where
  | atomic (thing : α) : RecursiveComponent α
  | complex (thing : α) (children : List (RecursiveComponent α)) :
      RecursiveComponent α
```

This captures:

- **The two-case distinction**: A component is either atomic (no further decomposition) or complex (has sub-components). This is Mobus's core structural insight — systemness is recursive, and recursion terminates at atomic work processes.

- **Structural well-foundedness**: Because `RecursiveComponent` is an inductive type, Lean's kernel guarantees that any recursive function over it terminates. There is no possibility of infinite decomposition. This is Showcase Theorem #6 — termination is a *property of the type*, not an axiom you assert.

- **Tree shape**: The type supports `depth` (line 72–74) and `atomicCount` (line 77–79), both computed by structural recursion. These characterize the decomposition hierarchy quantitatively.

What `RecursiveComponent` does **not** carry:

- **No network among children**: The `children` field is a `List`, not a graph. There is no representation of how sibling components interact. In Mobus's framework, the internal network N describes exactly these sibling interactions.

- **No boundary**: There is no distinction between interface components and internal components. Mobus's B = ⟨P, I⟩ (properties + interfaces) has no analog.

- **No environment**: A complex component has children but no environment. In Mobus's framework, the sibling components at the parent level *become* the decomposed component's environment objects.

- **No transforms**: There is no representation of what a component *does* — no transformation function, no flow processing, no state change. The component is purely structural.

In short, `RecursiveComponent` captures the **tree skeleton** of Mobus's recursive decomposition — the shape of the hierarchy — but not the **system semantics** at each node.

---

## 2. What Mobus Actually Means by Eq. 4.3

Mobus's recursive equation is deceptively simple:

> c_{i,j,l} = S_{i,j,l+1}  if component is complex
> c_{i,j,l} = a             if component is atomic

The key phrase is `c = S` — a complex component *is* a full system. Specifically, it gets its own 8-tuple:

> c_{i,j,l} = ⟨C, N, E, G, B, T, H, Δt⟩_{i,j,l+1}

This means:

1. **The component has its own composition C**: its sub-components at level l+1.

2. **The component has its own internal network N**: how those sub-components interact with each other. This is the network that `RecursiveComponent.children` (a flat list) does not capture.

3. **The component has its own environment E**: the sibling components at the parent level. When you "zoom into" component c_{i,j,l}, the other components of the parent system (c_{i,k,l} for k ≠ j) become external objects.

4. **The component has its own boundary-crossing flows G**: these correspond to the parent's internal network N restricted to edges involving c_{i,j,l}. The parent's *internal* flows become the child's *external* flows.

5. **The component has its own boundary B**: the interfaces through which flows from siblings enter and exit.

6. **The component has its own transforms T, history H, and time scale Δt**: potentially different dynamics at the lower level.

Mobus writes: the component is "treated as a new system of interest at the l+1 level." This is not metaphorical — the component literally instantiates the full system definition at a finer grain.

The implication for formalization is clear: a faithful `MobusSystem` type must allow its components to themselves be `MobusSystem`s. This is mutual recursion.

---

## 3. The Mutual Recursion Problem

A faithful formalization of Mobus Eq. 4.3 requires:

```
-- Pseudocode (not valid Lean as written)
structure MobusSystem (α : Type*) where
  components : List (MobusComponent α)
  network : ComponentGraph α
  environment : ...
  ...

inductive MobusComponent (α : Type*) where
  | atomic (thing : α) (process : AtomicProcess)
  | complex (subsystem : MobusSystem α)
```

`MobusSystem` contains `MobusComponent`s, and `MobusComponent` contains `MobusSystem`s. This is mutual induction.

Lean 4 supports mutual inductive types, but they come with trade-offs. Here are three design options, ranging from most faithful to most pragmatic.

### Option A: Mutual Inductive

```
mutual
  inductive MobusSystem (α : Type*) where
    | mk (components : List (MobusComponent α))
         (network : ...) (environment : ...) ...

  inductive MobusComponent (α : Type*) where
    | atomic (thing : α) (process : AtomicProcess)
    | complex (thing : α) (subsystem : MobusSystem α)
end
```

**Pros**: Most faithful to Mobus. The type *is* the recursion — a system is its components, each of which may be a system.

**Cons**: Mutual inductive types in Lean 4 generate a single combined recursor. Proving anything about `MobusSystem` requires simultaneously proving it about `MobusComponent`, and vice versa. Every theorem becomes a mutual induction. This is tractable but significantly harder than working with non-mutual types.

Additionally, Lean's `structure` command does not support mutual definitions — you must use `inductive` with explicit constructors, losing the field-name syntax and projection functions that make structures ergonomic.

### Option B: Indexed Reference

Keep the tree skeleton in `RecursiveComponent` and attach system data via a separate function:

```
structure MobusSystemData (α : Type*) where
  network : ComponentGraph α
  environment : Set α
  boundary : ...
  transforms : ...
  ...

def systemAt : RecursiveComponent α → MobusSystemData α := ...
```

**Pros**: Separates tree structure (which is already formalized and well-behaved) from system semantics (which are new). Avoids mutual recursion entirely — `RecursiveComponent` carries the shape, `systemAt` provides the content.

**Cons**: The system data at each node is not *part of* the component — it's computed after the fact. This means you can construct a `RecursiveComponent` tree and then separately argue about what system data it should carry, but the type system doesn't enforce consistency between the tree and the data.

### Option C: Phase-Split (Recommended for Phase 2)

Phase 2 defines `MobusSystem` as a flat structure with `components : Set α` (like Bunge's C) — no recursion in the type. A separate `Decomposition` structure connects `MobusSystem` to `RecursiveComponent` post hoc:

```
structure MobusSystem (α : Type*) where
  components : Set α
  network : Set (α × α)      -- internal component interactions (N)
  environment : Environment α  -- ⟨O, M⟩
  externalFlows : Set (α × α) -- boundary-crossing flows (G)
  boundary : Boundary α        -- ⟨P, I⟩
  transforms : α → α → α      -- parametric (T)
  history : Set α              -- knowledge encoding (H)
  timeScale : ℕ               -- Δt

structure DecompositionWitness (α : Type*) where
  system : MobusSystem α
  tree : RecursiveComponent α
  consistent : -- leaves of tree ↔ atomic members of system.components
               -- complex nodes ↔ subsystems with their own MobusSystem
  ...
```

**Pros**: Simplest for the compiler. `MobusSystem` is a plain structure with no recursion — easy to construct, easy to reason about. The recursive nature of decomposition is captured by `DecompositionWitness`, which connects a flat system to a tree *after both are independently defined*. This is the standard mathematical approach: define the objects first, then state theorems about their relationships.

**Cons**: Less elegant than Option A — the recursion is an external property, not built into the type. You can construct a `MobusSystem` that has no well-founded decomposition, and nothing in the type prevents it. The `DecompositionWitness` is a *proof obligation*, not a *structural guarantee*.

### Recommendation

**Option C for Phase 2** (workshop paper timeline), with a note that **Option A is the eventual target** for the journal submission.

Rationale:
- Option C gets the bridge theorem (`MobusSystem ↔ ConcreteSystem`) and showcase results (atomic process classification, decomposition well-foundedness) without fighting mutual induction.
- The bridge theorem operates on the *flat tuple*, not on the recursion — it compares `MobusSystem.components` to `ConcreteSystem.composition`, etc. Decomposition is a separate theorem that doesn't need to be entangled with the bridge.
- Option A is architecturally correct but high-friction for a workshop paper. It would be worth the investment for a journal where the recursive structure itself is a contribution.

---

## 4. Atomic Work Processes

Mobus identifies five atomic processes that serve as recursion terminators. When a component is classified as one of these five, decomposition stops — no further internal structure is meaningful.

### The Five Processes

| Process | Inputs | Outputs | Semantics |
|---------|--------|---------|-----------|
| **Combine** | 2+ flows in | 1 flow out | Merge multiple inputs into a single output (e.g., chemical reaction, assembly line convergence) |
| **Split** | 1 flow in | 2+ flows out | Divide a single input into multiple outputs (e.g., distribution, branching) |
| **Impede** | 1 flow in | 1 flow out | Reduce flow rate (e.g., resistance, friction, regulatory bottleneck) |
| **Propel** | 1 flow in | 1 flow out | Increase flow rate (e.g., pump, catalyst, amplifier) |
| **Buffer** | 1 flow in | 1 flow out | Temporal storage — absorb flow, release later (e.g., reservoir, inventory, cache) |

Key observations:
- **I/O topology distinguishes them**: Combine and split differ by arity direction. Impede and propel differ by rate effect. Buffer differs by temporal storage.
- **They are recursion terminators**: If a component implements one of these five, it is atomic by definition — the analysis stops here.
- **Mobus does not give them mathematical transfer functions** in Ch. 4. The semantics are described informally. Formalizing their transfer functions requires domain-specific content (what does "impedance" mean in a biological vs. economic context?).

### Lean Formalization

The natural encoding is an enumeration with I/O arity constraints:

```
inductive AtomicProcess where
  | combine   -- 2+ inputs, 1 output
  | split     -- 1 input, 2+ outputs
  | impede    -- 1 input, 1 output (rate reduction)
  | propel    -- 1 input, 1 output (rate increase)
  | buffer    -- 1 input, 1 output (temporal storage)
```

The arity constraints (combine needs ≥2 inputs, etc.) would be captured by a separate structure:

```
structure AtomicProcessSpec where
  process : AtomicProcess
  minInputs : ℕ
  minOutputs : ℕ
  arityValid : match process with
    | .combine => minInputs ≥ 2 ∧ minOutputs = 1
    | .split => minInputs = 1 ∧ minOutputs ≥ 2
    | .impede => minInputs = 1 ∧ minOutputs = 1
    | .propel => minInputs = 1 ∧ minOutputs = 1
    | .buffer => minInputs = 1 ∧ minOutputs = 1
```

The transfer functions remain parametric — `T : InputType → OutputType` — until a domain provides concrete semantics.

### Connection to RecursiveComponent

The existing `RecursiveComponent.atomic` wraps a bare thing:

```
-- Level.lean:55
| atomic (thing : α) : RecursiveComponent α
```

A refined version would attach the process classification:

```
-- Phase 2 refinement (not yet implemented)
| atomic (thing : α) (process : AtomicProcess)
```

Or, to support domain-specific stopping criteria alongside process classification:

```
| atomic (thing : α) (process : Option AtomicProcess)
```

where `none` means "atomic by domain convention" (e.g., a transistor in a circuit model) and `some p` means "atomic because it implements primitive process p."

---

## 5. Connection Plan for Phase 2

### What Stays

`RecursiveComponent` in Level.lean stays as-is. It correctly captures the tree shape of decomposition, and its well-foundedness (guaranteed by the inductive type) is a structural result that doesn't depend on system semantics. Phase 2 builds *on top of* it, not *in place of* it.

### What Gets Added

A new file `Systems/Mobus/Decomposition.lean` provides:

1. **`AtomicProcess` inductive type** — the five-process enumeration described in §4.

2. **`DecompositionWitness`** — connects a `MobusSystem` to a `RecursiveComponent` tree that is consistent with its component set:
   - The leaves of the tree correspond to atomic members of the system's components
   - Each complex node corresponds to a subsystem that can be independently described as a `MobusSystem`
   - The tree's `atomicCount` equals the cardinality of the atomic component subset

3. **Leaf characterization theorem** — "the leaf nodes of the decomposition tree are exactly the atomic components":
   ```
   theorem leaves_eq_atomic (w : DecompositionWitness α) :
     leaves w.tree = atomicComponents w.system
   ```

4. **Well-foundedness theorem** — "every `MobusSystem` admits a well-founded recursive decomposition whose leaves are atomic processes":
   ```
   theorem decomposition_terminates (w : DecompositionWitness α) :
     ∀ leaf ∈ leaves w.tree, leaf.isAtomic = true
   ```
   This follows immediately from the inductive type but is worth stating explicitly as a theorem for the paper.

### What Does Not Need to Change

The **bridge from `MobusSystem` → `ConcreteSystem`** (planned for Bridge.lean) operates on the flat tuple:

- `MobusSystem.components` maps to `ConcreteSystem.composition`
- `MobusSystem.environment.objects` maps to `ConcreteSystem.environment`
- `MobusSystem.network ∪ MobusSystem.externalFlows` maps to `ConcreteSystem.structure'`

This bridge does *not* need to know about decomposition. It works at a single level of the hierarchy, comparing two system representations (Mobus's 8-tuple and Bunge's CES triple) at the same level.

The decomposition story is orthogonal: "every `MobusSystem` can be recursively decomposed" is a separate theorem that says something about the *internal* structure of a system, not about how it relates to Bunge's framework.

### Dependency Graph (Phase 2 Addition)

```
Phase 1 (existing):
  Thing → Bond → System → Level (contains RecursiveComponent)
                    │
                    ├→ Assembly
                    ├→ Selection
                    └→ State

Phase 2 (new):
  System ──→ Mobus/Core.lean (MobusSystem 8-tuple)
               │
               ├→ Mobus/Bridge.lean (MobusSystem ↔ ConcreteSystem)
               └→ Mobus/Decomposition.lean (AtomicProcess + DecompositionWitness)
                    │
                    └── uses Level.lean's RecursiveComponent
```

The Phase 2 modules depend on Phase 1 but do not modify it. `RecursiveComponent` is consumed by Decomposition.lean, not altered.

---

## Summary

| Aspect | Phase 1 (Current) | Phase 2 (Planned) |
|--------|-------------------|-------------------|
| Tree structure | `RecursiveComponent` ✓ | Unchanged |
| System tuple | Bunge CES triple | Mobus 8-tuple (`MobusSystem`) |
| Atomic processes | Bare `thing : α` | `AtomicProcess` enum with arity |
| Decomposition | Structural (inductive type) | Semantic (`DecompositionWitness` linking system to tree) |
| Network among siblings | Not represented | `MobusSystem.network` |
| Environment | `ConcreteSystem.environment` (flat set) | `Environment α` = ⟨O, M⟩ |
| Recursion strategy | N/A — tree is non-mutual | Option C (flat system + external decomposition proof) |
| Bridge to Bunge | N/A | `Bridge.lean` (tuple field correspondence) |
