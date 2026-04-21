import VersoManual
import Systems.Examples.Thermostat
import Systems.Klir.KlirSystem

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Systems
open Systems.Examples

set_option pp.rawOnError true

#doc (Manual) "The Commuting Triangle" =>

Bunge (1979) read Klir — he cites Klir and Valach (1967) and Klir and Rogers (1977) in his bibliography. Mobus (2022) read Klir — he cites Klir (2001) explicitly. **Neither Bunge nor Mobus references the other.** They developed independently from a shared Klir root, 43 years apart, using different notation, terminology, and motivating examples.

The formalization discovers that both paths from Mobus's 8-tuple back to Klir's $`(T, R)` — via Bunge or directly — produce the same result. Not merely the same up to isomorphism. *Definitionally identical.*

# The Projection Maps

**Bunge → Klir** (forget environment):
- $`T := C` — things are the components
- $`R := S` — relation is the structure

```lean
#check @ConcreteSystem.toKlir
```

**Mobus → Bunge** (forget milieu, capacity, boundary, transforms, history, time scale):
- $`C := C` — components are exact
- $`E := O` — environment is the discrete objects (milieu $`M` discarded)
- $`S := N.\text{toRelation} \cup G.\text{toRelation}` — capacity $`\kappa` discarded

```lean
#check @MobusSystem.toBunge
```

**Mobus → Klir** (forget everything except $`T` and $`R`):

```lean
#check @MobusSystem.toKlir
```

# The Theorem

```lean
#check @triangle_commutes
```

The proof is `rfl` — *reflexivity*. The Lean type-checker confirms that the two paths produce not just equal but definitionally identical `KlirSystem` values. No proof search, no simplification, no rewriting. The two expressions reduce to the same normal form.

This traces to both Bunge and Mobus inheriting $`T` = `Set α` and $`R` = `Set (α × α)` from Klir without changing the mathematical type. Neither author knew this about the other's work. It was *discovered* through formalization.

# Information Loss

The bridge is a projection: many Mobus 8-tuples map to the same Bunge triple. Six categories of information have no Bunge counterpart:

- **Milieu** $`M` — Ambient conditions (temperature, pressure). Bunge's $`E` is a set of things only.
- **Capacity** $`\kappa` — How much flows (BTUs, bits, dollars). Bunge's $`S` is pairs, not weighted.
- **Boundary properties** $`\pi` — Permeability, insulation. Bunge has no boundary concept.
- **Transforms** $`\tau` — What things *do* to their inputs. No functional component in Bunge.
- **History** $`\eta` — Accumulated knowledge. No memory component in Bunge.
- **Time scale** $`\delta` — Temporal resolution. Time-indexed but unformalized in Bunge.

Two Mobus systems differing only in these six categories project to the **same** Bunge CES triple. This is *independent convergence with formally characterized divergence*.
