# Simon's Argument, Formalized

*How "The Architecture of Complexity" decomposes under machine-checked proof*

**Last updated**: 2026-05-24
**Lean sources**: `Systems/Core/Level.lean`, `Systems/Core/Dynamics.lean`
**Companion**: `principles-formalization-companion.md`

---

## Simon's Original Argument (1962)

Herbert Simon, "The Architecture of Complexity," observes that complex systems in nature — cells, organisms, economies, organizations — are hierarchically organized. His key claim: this is not accidental. Hierarchical systems are the ones that can evolve, because they are **nearly decomposable**:

1. Components cluster into modules
2. Within-module interactions are much stronger than between-module interactions
3. **Therefore** modules reach internal equilibrium fast
4. **Therefore** inter-module dynamics are slow
5. **Therefore** time-scale separation: fast micro-dynamics, slow macro-dynamics
6. **Therefore** you can understand the system level by level

This is the most cited structural argument in systems science. Mobus builds on it (Ch. 4). Bunge references it. Everyone uses it. Nobody formalized it — until now.

---

## What Bunge, Mobus, and Klir Provide

**Bunge** (1979) gives the CES triple — composition, environment, structure. This defines what a system IS: bounded, organized, with internal bonds. No dynamics, no time scales, no modules.

**Mobus** (2022) extends Bunge to the 8-tuple — adding flow networks, boundaries, transforms, history, time scale as a parameter. He references Simon extensively but doesn't formalize the argument. He describes near-decomposability informally and asserts time-scale separation.

**Klir** gives S = (T, R) — the walking arrow, the irreducible common core. A system is things with relations on them.

None of these traditions PROVE Simon's claim. They cite it, build on it, assume it. The argument lives in English prose, not in mathematics.

---

## The Formalized Chain

We built Simon's argument as a chain of formal structures in Lean 4, each connecting to the next. The chain identifies exactly what each principle contributes and where the assumptions live.

### Step 1: NearDecomposable (Hierarchy #2)

*Source: Level.lean*

Formalizes the structural claim. A system is near-decomposable when its composition partitions into modules where within-module interaction uniformly exceeds between-module interaction, separated by a threshold.

```
NearDecomposable σ T :=
  modules : List (Set α)
  threshold : T
  within_strong : ∀ within-module pair, strength ≥ threshold
  between_weak : ∀ between-module pair, strength < threshold
```

**What this captures**: Simon's step 1-2. The partition into modules with the strong/weak interaction distinction.

### Step 2: within_exceeds_between (Hierarchy #2)

*Source: Level.lean, theorem*

Proves: in any near-decomposable system, for any within-module pair (a, b) and between-module component c, the within-module interaction is strictly stronger than the cross-module interaction.

**What this captures**: Simon's informal claim made precise. "Modules are internally cohesive and externally loosely coupled."

### Step 3: conditional_time_scale_separation (Hierarchy #2 → Dynamics #4)

*Source: Level.lean, theorem*

**THE GAP.** Simon jumps from "stronger interaction" (structural) to "faster dynamics" (temporal). This jump requires an assumption he never stated:

> There must exist a strictly anti-monotone map from interaction strength to characteristic time scale.

Formally: `StrictAnti f` where `f : InteractionStrength → TimeScale`.

The theorem proves: IF this map exists, THEN near-decomposability implies within-module dynamics are strictly faster than between-module dynamics.

**What this captures**: Simon's step 2→3. The finding: this is a CONDITIONAL, not a theorem. The assumption is the bridge between structure and dynamics. Simon left it implicit.

**When it applies**: Domains where stronger coupling produces faster dynamics — springs, circuits, markets, neural networks. **When it doesn't**: Domains where coupling strength and dynamical speed are independent — tectonic plates, certain institutional systems.

### Step 4: InteractionDynamicsBridge (Dynamics #4)

*Source: Dynamics.lean, structure*

Names the structure that provides the StrictAnti map. This is what Dynamics (#4) contributes to Hierarchy (#2):

```
InteractionDynamicsBridge T S :=
  toTimeScale : T → S
  strictAnti : StrictAnti toTimeScale
```

**What this captures**: The physical content of Dynamics as it relates to Simon. Without this bridge, hierarchy is two disconnected claims: "modules exist" and "levels are fast/slow." The bridge connects them.

### Step 5: CoupledDynamicSystem (Dynamics #4)

*Source: Dynamics.lean, structure*

Formalizes what it means for subsystems to influence each other's state:

```
CoupledDynamicSystem α S₁ S₂ :=
  system : ConcreteSystem α
  law₁ : S₁ → S₂ → S₁   -- subsystem 1's evolution depends on both states
  law₂ : S₁ → S₂ → S₂   -- subsystem 2's evolution depends on both states
```

Independent dynamics (zero coupling) is the special case where `law₁` ignores `S₂` and `law₂` ignores `S₁`.

**What this captures**: The distinction between independent and coupled evolution that Simon's argument requires.

### Step 6: TimescaleDecomposition (Dynamics #4)

*Source: Dynamics.lean, structure + theorems*

The decomposition Simon describes. Given a coupled system and a reference equilibrium:

- **Fast dynamics**: freeze the other subsystem at equilibrium, evolve independently. This is the "within-module" evolution — what each module does when the rest of the system is held fixed.
- **Slow dynamics**: the full coupled evolution, including between-module coupling.

```
TimescaleDecomposition S₁ S₂ :=
  fast₁ : S₁ → S₁     -- within-module 1
  fast₂ : S₂ → S₂     -- within-module 2
  slow : S₁ × S₂ → S₁ × S₂  -- full coupled
```

**Key theorems**:
- The reference equilibrium IS a fixed point of both fast dynamics (`decompose_fast₁_equilibrium`, `decompose_fast₂_equilibrium`). The product equilibrium is what fast dynamics converges TO.
- At the equilibrium, the slow dynamics is also stationary (`decompose_slow_at_equilibrium`).
- For independent dynamics (zero coupling), the fast laws ARE the original subsystem laws (`decompose_independent_fast₁`, `decompose_independent_fast₂` — both by `rfl`).

**What this captures**: Simon's steps 3-5. The structural skeleton of "fast dynamics converges, then slow dynamics operates on the equilibrium manifold."

---

## What We Found That Simon Didn't State

### Finding: The gap has a name

`StrictAnti f` — stronger interaction produces faster dynamics. Simon assumed this universally. The formalization isolates it as a separable assumption. It tells you WHEN Simon's argument applies (domains where coupling → speed) and WHEN it breaks (domains where coupling and speed are independent).

### Finding: The decomposition is universal; the quality guarantee is conditional

You can decompose ANY coupled system into fast/slow components around any equilibrium. The decomposition doesn't need near-decomposability to DEFINE. Near-decomposability is what guarantees the decomposition is a GOOD approximation — that the fast dynamics dominates at short time scales. This is a separation of concerns that Simon's prose conflates.

### Finding: The dynamics hierarchy is fixed-point approximations

Product equilibria (zeroth order, independent) → coupled equilibria (exact, coupled). The gap between them measures coupling strength. Near-decomposability bounds this gap. Multi-timescale analysis IS perturbation theory on equilibria, parameterized by coupling strength.

### Finding: No single principle produces multi-timescale behavior

Systemness gives composition. Hierarchy gives modules. Dynamics gives the bridge. Time-scale separation emerges from their INTERACTION, not from any one principle alone. The architecture of Simon's argument IS the dependency structure of the principles.

---

## What Remains

The **quantitative** result: proving that the fast dynamics CONVERGES to the equilibrium and that the slow dynamics well-approximates the full coupled dynamics near the equilibrium manifold. This requires:

- A metric on state space (to define "close to")
- A stability condition on the fast equilibrium (attracting, not just fixed)
- A bound on coupling strength from NearDecomposable.threshold

This is the point where the formalization would need Mathlib's metric space infrastructure. The structural skeleton — which assumptions are needed, what connects to what, where the gaps are — is complete.

---

## Connection to K ≅ 2

The common core theorem (K ≅ **2**) says: a system, across all seven traditions, is a morphism — relations depend on things. Simon's argument is about what happens when you have MANY such morphisms (many interacting things) organized hierarchically. The walking arrow is the atom; Simon's architecture is the molecule. The formalization builds the molecule from atoms using the composition closure theorem and the interaction-dynamics bridge.
