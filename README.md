# Systems Ontology — Lean 4 Formalization

Machine-verified formalization of seven independently developed systems ontology frameworks, proving they share a common categorical core.

```
        Klir (1969/2001)
       S = (T, R)
      ╱             ╲
    adds E          adds flows, boundary,
  (environment)     milieu, transforms,
    ╱               history, time scale
   ╱                   ╲
Bunge (1979)          Mobus (2022)
⟨C, E, S⟩             ⟨C, N, E, G, B, T, H, Δt⟩
   ╲                   ╱
    ╲    toBunge      ╱
     ╲ ─────────── ╱
      ╲           ╱
       ╲         ╱
        ╲       ╱
    Mobus→Bunge→Klir
         =             ← proof: rfl
    Mobus→Klir
```

Klir defined a system as a set of things and a relation. Bunge added environment. Mobus added typed flows, boundaries, transforms, history, and time scale. Neither Bunge nor Mobus references the other --- they developed independently from the shared Klir root, 43 years apart. The Lean proof assistant confirms: both paths from the 8-tuple back to (T, R) produce *definitionally identical* results.

This was not claimed by any of the three authors. It was *discovered* through formalization.

**~4,700 lines | 34 files | zero `sorry`s | 7 traditions | 12 headline results**

## What Formalization Revealed

The compiler told us things about these ontologies that decades of reading had not:

- **A logical error in Bunge (1979)**: Def 1.6 describes the subsystem relation as "reflexive, asymmetric, and transitive." A relation cannot be both reflexive and asymmetric. He means *antisymmetric* --- a partial order. In print 47 years.

- **Cross-volume dependency architecture**: Bunge's Corollary 1.1 ("the universe is the only closed system") is a tautology without Postulate 5.10 from Vol. 3 --- a dependency invisible in prose but undeniable in the type system.

- **Independent convergence with formally characterized divergence**: Six categories of information in Mobus's 8-tuple have no Bunge counterpart. These mark precisely where the engineering tradition elaborated concepts the philosophical tradition did not require.

- **Clean compositions as empirical findings**: Selection composition proves by `rfl`. Emergence decomposes via `simp`. Boundary completeness follows as a free structural consequence. The right representations make deep theorems definitionally true.

## Headline Results

1. **Commuting triangle** --- Mobus → Bunge → Klir = Mobus → Klir, proof: `rfl`
2. **Common core theorem** --- K ≅ **2**: Klir's walking arrow embeds faithfully into all 7 shape categories. The irreducible content of "system" across 60 years is a single morphism: *relations depend on things.*
3. **Bridge theorem** --- every Mobus 8-tuple projects to a valid Bunge CES triple, preserving subsystem order
4. **Bunge correction** --- subsystem relation is a partial order, not "reflexive and asymmetric"
5. **Shape category landscape** --- 7 traditions encoded as free categories on dependency quivers; structural/operational/cybernetic divide diagnosed by arrow direction
6. **Bridge factorization** --- `toBunge = toRichBunge ⋙ flatten`: the Mobus→Bunge passage factors through the structure family

## Reading the Formalization

The flagship document --- *Foundations for Mathematical Systems Science: Seven Traditions, One Theorem* --- is built with [Verso](https://github.com/leanprover/verso) and renders the Lean source as interactive HTML with hover-inspectable types. See `docs/verso/` to build locally.

## Building

Requires Lean 4 (v4.28.0) and Mathlib:

```bash
lake update   # fetch Mathlib (first time only)
lake build    # compile all 34 modules — must pass with zero errors
```

## Related

- [BERT](https://github.com/halcyonic-systems/bert) --- Systems analysis tool implementing Mobus's framework. The Lean proofs provide machine-checked foundations for the same concepts BERT implements visually.

## License

MIT
