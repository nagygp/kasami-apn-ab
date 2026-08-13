# Dependency Graph: `mcm_permutation`

This document describes the current proof of `Dobbertin1999.MCM.mcm_permutation`
in [Dobbertin1999MVP/Dobbertin1999/MCM.lean](Dobbertin1999MVP/Dobbertin1999/MCM.lean).

For $F = \mathbb{F}_{2^n}$, the implemented MCM polynomial is

$$
\operatorname{MCMpol}_{n,m}(x)
= L_m(x)^{2^m+1}x^{(2^n-1)-2^m},
\qquad
L_m(x)=\sum_{i=0}^{m-1}x^{2^i}.
$$

Thus it is the polynomial representative of
$L_m(x)^{2^m+1}/x^{2^m}$, including at $x=0$.  The theorem assumes
$0 < m < n$, both $m$ and $n$ odd, and $\gcd(m,n)=1$.

```mermaid
flowchart TD
  Goal["mcm_permutation\nMCMpol n m is bijective"]
  Split{"m = 1?"}
  One["m = 1 branch\nMCMpol n 1 = id"]
  OneTrace["truncTrace 1 x = x"]
  Frob["FiniteField.pow_card\nx^(2^n) = x"]
  General["m > 1 branch\nGold after Dempwolff-Muller"]

  Goal --> Split
  Split -->|yes| One
  OneTrace --> One
  Frob --> One
  Split -->|no| General
```

## Main Composition: $m > 1$

The proof obtains a linking exponent $k'$ with two modular properties.  One
property makes the Dempwolff-Muller map bijective; the other identifies the
MCM polynomial with its composition with the Gold power map.

```mermaid
flowchart TD
  Main["mcm_permutation\n(m > 1)"]
  Link["KasamiAPN.exists_linking_exp\nchoose k'"]
  Factor["MCM_eq_dempwolff_mueller_pow\nMCMpol(x) = (L_m(x) x^k')^(2^m+1)"]
  DM["dempwolff_mueller_permutation_ktransfer\nL_m(x) x^k' is bijective"]
  Gold["gold_permutation\ny -> y^(2^m+1) is bijective"]
  Compose["Function.Bijective.comp\nGold o Dempwolff-Muller"]

  Main --> Link
  Link --> Factor
  Link --> DM
  Factor --> Compose
  DM --> Compose
  Gold --> Compose
  Compose --> Main
```

The linking exponent carries these two congruences modulo $2^n-1$:

$$
k'(2^m+1) \equiv (2^n-1)-2^m,
$$

$$
(2^{n-1}-2^{m-1}-1)k' \equiv 2^{m-1}.
$$

The first is consumed by `MCM_eq_dempwolff_mueller_pow`; the second is
consumed by `dempwolff_mueller_permutation_ktransfer`.

## Dempwolff-Muller Core

The core theorem proves injectivity and obtains surjectivity from finiteness.
For injectivity it separates the zero and nonzero cases.  The zero cases use
triviality of the kernel of $L_m$; the nonzero case reduces equality of MCM
values to equality under a Dickson-like polynomial, whose restriction to the
units is injective.

```mermaid
flowchart TD
  Bij["LxXk_bijective"]
  Inj["Injectivity of x -> L_m(x)x^k"]
  Surj["Finite.injective_iff_surjective\nSurjectivity"]
  Equal["Assume L_m(x)x^k = L_m(y)y^k"]
  Cases{"x = 0 or y = 0?"}
  Kernel["truncTrace_ker_trivial\nL_m(z)=0 implies z=0"]
  Units["LxXk_injective_on_units\nnonzero x,y imply x=y"]
  Result["x = y"]

  Bij --> Inj --> Surj --> Bij
  Equal --> Cases
  Cases --> Kernel --> Result --> Inj
  Cases --> Units --> Result
```

## Unit Case and Dickson Reduction

```mermaid
flowchart TD
  UnitInj["LxXk_injective_on_units"]
  Exp["Finite-field exponent identity\nx^(2k) x^(2^m+1) = 1"]
  Square["Square the assumed equality"]
  Reduce["truncTrace_sq_mul_inv_eq_dicksonF\nrewrite as dicksonF(m, x^-1) = dicksonF(m, y^-1)"]
  DicksonInj["dicksonF_injective_on_units"]
  UnitsEqual["x^-1 = y^-1"]
  Equal["x = y"]

  UnitInj --> Exp --> Square --> Reduce --> DicksonInj --> UnitsEqual --> Equal
```

## Support for the Two Main Reductions

```mermaid
flowchart TD
  Kernel["truncTrace_ker_trivial"]
  Telescoping["truncTrace_sq_add_self\nL_m(x)^2 + L_m(x) = x^(2^m) + x"]
  Fixed["frob_fixed_of_truncTrace_zero\nL_m(x)=0 implies x^(2^m)=x"]
  FieldFrob["FiniteField.pow_card\nx^(2^n)=x"]
  Gcd["Coprime m n\ncommon Frobenius fixed points lie in F_2"]
  One["truncTrace_one_eq_one\nL_m(1)=1 for m odd"]

  Kernel --> Fixed
  Fixed --> Telescoping
  Kernel --> FieldFrob
  Kernel --> Gcd
  Kernel --> One

  Dickson["dicksonF_injective_on_units"]
  Rep["exists_add_inv_rep\nrepresent x as z + z^-1"]
  Functional["dicksonF_functional\nf_m(z + z^-1) = z^(2^m-1) + z^-(2^m-1)"]
  Symmetry["eq_or_eq_inv_of_add_inv_eq"]
  QuadFrob["frob_2n_eq_self_of_quad_root"]
  Mersenne["coprime_mersenne_double'\nCoprime (2^m-1) (2^(2n)-1)"]
  DicksonResult["Dickson equality forces x=y"]

  Dickson --> Rep
  Dickson --> Functional
  Dickson --> Symmetry
  Dickson --> QuadFrob
  Dickson --> Mersenne
  Rep --> Functional --> Symmetry --> DicksonResult
  QuadFrob --> Mersenne --> DicksonResult
```

## Dempwolff-Muller $k'$ Transfer

The MCM proof uses the transfer form, exposed as
`dempwolff_mueller_permutation_ktransfer`.  Its finite-field proof reduces back
to the canonical Dempwolff-Muller result `LxXk_bijective` using the
Frobenius-adjoint machinery.

```mermaid
flowchart LR
  Transfer["dempwolff_mueller_permutation_ktransfer"] --> KPrime["LxXk'_bijective"]
  KPrime --> Base["LxXk_bijective"]
  KPrime --> Adj["adjoint_swap_bij\nfrobSum_adjoint_Ico\ntrace_nondegenerate"]
  KPrime --> Frob["truncTrace_adj_frob\nfrob_comp_bijective_right"]
```

## Source Map

- The project-level MCM wrapper is [Dobbertin1999MVP/Dobbertin1999/MCM.lean](Dobbertin1999MVP/Dobbertin1999/MCM.lean).
- The main argument, truncated-trace lemmas, Dickson reduction, and Theorem 3.2 are in [Dobbertin1999MVP/FiniteField/Thm32.lean](Dobbertin1999MVP/FiniteField/Thm32.lean).
- The $k'$ transfer-only adjoint facts come from [Dobbertin1999MVP/FiniteField/AdjointBij.lean](Dobbertin1999MVP/FiniteField/AdjointBij.lean), [Dobbertin1999MVP/FiniteField/FrobAlg.lean](Dobbertin1999MVP/FiniteField/FrobAlg.lean), and [Dobbertin1999MVP/FiniteField/TraceNorm.lean](Dobbertin1999MVP/FiniteField/TraceNorm.lean).
