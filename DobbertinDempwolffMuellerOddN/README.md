This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Dobbertin (1999) — MCM · MCM → APN · APN (standalone MVP)

A **self-contained, minimal** Lean 4 formalisation of the **MCM**, **MCM → APN**,
and **APN** parts of

> Hans Dobbertin, *"Kasami Power Functions, Permutation Polynomials and Cyclic
> Difference Sets"*, in *Difference Sets, Sequences and their Correlation
> Properties*, NATO Sci. Ser. C **542**, Kluwer Academic Publishers, 1999,
> pp. 133–158.

This folder is a stand-alone extract of the larger `RequestProject` development.
It imports **only** the modules that actually contribute to the three headline
transcriptions, plus their finite-field prerequisites — nothing from the Walsh /
almost-bent / difference-set layers is pulled in. The whole chain is
`sorry`-free and rests only on the standard axioms `propext`, `Classical.choice`,
`Quot.sound`.

## Entry point

`../DobbDempMue.lean` (Lean module `DobbDempMue`). Building it:

```
lake build DobbDempMue
```

## Headline results

Exposed under namespace `Dobbertin1999.Headlines` (in the entry file):

| Alias | Statement |
|---|---|
| `mcm_permutation` | Müller–Cohen–Matthews: `x ↦ L_m(x)·x^{2^{n-1}−2^{m-1}−1}` permutes `𝔽_{2ⁿ}` |
| `mcm_permutation_ktransfer` | the `k'`-transfer form consumed by the APN chain |
| `kasami_key_identity` | `((x+1)^d + x^d + 1)·(x²+x)^{2^k} = (x^{2^k}+x)^{2^k+1}` |
| `kasami_is_apn` | **Corollary 2**: Kasami power functions are APN (collision form) |
| `kasami_is_apn_solution_count` | Corollary 2, Nyberg form: `0` or exactly `2` solutions |

## Module layout

```
DobbDempMue.lean                      -- entry point + headline aliases
DobbDempMue/
  FiniteField/                             -- finite-field engine
    ExpArith.lean                          -- exponent arithmetic
    FrobAlg.lean                           -- Frobenius algebra
    TraceNorm.lean                         -- trace / norm
    AdjointBij.lean                        -- additive-adjoint bijection
    BareLemma31Skeleton.lean               -- Lemma 3.1 skeleton
    Thm32.lean                             -- MCM permutation theorem (theorem_3_2)
  Core/
    KasamiAPN.lean                         -- Kasami APN engine over the MCM theorem
  Dobbertin1999/
    MCM.lean                               -- MCM permutation polynomial (Section 2)
    MCMtoAPN.lean                          -- bridge used in the proof of Corollary 2
    APN.lean                               -- Corollary 2: Kasami power functions are APN
```

## The MCM → APN chain

```
MCM.mcm_permutation_ktransfer         (Müller–Cohen–Matthews engine)
        ▼
MCMtoAPN.kasami_key_identity          (Kasami derivative ↔ Gold exponent)
MCMtoAPN.gold_permutation             (y ↦ y^{2^k+1} bijective)
MCMtoAPN.mcm_injective_bridge         (MCM ∘ Gold injectivity)
MCMtoAPN.kasami_collision_forces_equal_u   (collision ⟹ x²+x = y²+y)
        ▼
APN.kasami_is_apn / kasami_is_apn_solution_count   (Corollary 2)
```
