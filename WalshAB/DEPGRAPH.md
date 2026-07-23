# Dependency Graph

This document records the dependency path for the project target
`KasamiAB.kasami_is_ab` as of 2026-07-23.

## Build Target

`lakefile.lean` declares the `AlmostBent` library as Lake's default target.
Its roots are:

```text
AlmostBent.Defs
AlmostBent.CharTwoBasics
AlmostBent.CrossForm
AlmostBent.QuadraticDivisibility
AlmostBent.WalshDiv
AlmostBent.WalshLayers
AlmostBent.KasamiAB
```

The main theorem is in `AlmostBent.KasamiAB`.

## Module Imports

```mermaid
graph TD
  KAB[AlmostBent.KasamiAB]
  WL[AlmostBent.WalshLayers]
  CF[AlmostBent.CrossForm]
  WD[AlmostBent.WalshDiv]
  QD[AlmostBent.QuadraticDivisibility]
  CT[AlmostBent.CharTwoBasics]
  DEF[AlmostBent.Defs]
  M[Mathlib]

  KAB --> WL
  KAB --> CF
  KAB --> WD

  WD --> QD
  WD --> DEF
  QD --> WL
  QD --> DEF
  CF --> CT
  CT --> DEF
  WL --> DEF

  DEF --> M
  QD --> M
  WD --> M
  WL --> M
```

`AlmostBent.KasamiAB` reaches every module needed by its proof through its
three direct imports: `WalshLayers`, `CrossForm`, and `WalshDiv`.

## Main Proof Dependencies

```mermaid
graph TD
  TARGET[kasami_is_ab]

  TARGET --> AB[WalshAB.ab_from_moments]
  TARGET --> BIJ[KasamiAB.kasami_bijective]
  TARGET --> APN[KasamiAB.kasami_is_apn_pred]
  TARGET --> DIV[KasamiWalshDiv.kasami_walsh_div]

  BIJ --> INJ[KasamiAB.kasami_injective]
  INJ --> POW[CollisionAnalysis.pow_d_injective]
  INJ --> DPOS[CollisionAnalysis.d_pos]
  POW --> POWU[pow_d_injective_units]
  POWU --> COP[d_coprime_card_sub_one]
  COP --> D[CollisionAnalysis.d]
  DPOS --> D

  APN --> APN0[KasamiAB.kasami_apn]
  APN --> ISAPN[WalshAB.IsAPN]

  AB --> PARSEVAL[WalshAB.parseval_perm]
  AB --> FOURTH[WalshAB.fourth_moment_apn]
  AB --> ISAB[WalshAB.IsAB]

  PARSEVAL --> CHI[Tr, chi, walsh, chi_sum_eq]
  FOURTH --> MOMENT[autocorrelation and differential-count lemmas]
  MOMENT --> CHI

  DIV --> REWRITE[walsh_kasami_eq_quadratic]
  DIV --> GAUSS[WalshDivisibility.quadratic_gauss_sum_div]
  DIV --> DERIV[sum_gold_third_deriv_zero]
  REWRITE --> GOLDPERM[gold_pow_bijective]
  REWRITE --> DMG[d_mul_gold]
  DERIV --> GOLD3[third_deriv_gold_zero]
  GAUSS --> ADDCHAR[additive_char_sum_dvd]
  GAUSS --> VAL[dvd_of_sq_dvd_pow_two_odd]
```

## Proof Obligations Supplied to `ab_from_moments`

`kasami_is_ab` applies the general lattice argument with three facts about
`x |-> x ^ d k`:

| Obligation | Theorem used |
| --- | --- |
| Walsh second moment | `parseval_perm`, using `kasami_bijective` |
| Walsh fourth moment | `fourth_moment_apn`, using `kasami_bijective` and `kasami_is_apn_pred` |
| Walsh divisibility | `KasamiWalshDiv.kasami_walsh_div` |

## Verification Caveat

`AlmostBent.KasamiAB.kasami_apn` is currently closed with `sorry`.
Consequently, `kasami_is_ab` compiles, but its APN branch is admitted rather
than proved in the current source tree.
