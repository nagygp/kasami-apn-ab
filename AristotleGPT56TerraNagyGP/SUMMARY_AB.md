# Summary of Kasami AB formalization

This directory proves that the Kasami monomial

```text
x |-> x^d,    d = 2^(2k) - 2^k + 1,
```

is Almost Bent (AB) on `GF(2^n)` under the hypotheses

```text
0 < k < n,  gcd(k, n) = 1,  and  n is odd.
```

The main result is `KasamiAB.kasami_is_ab` in `AlmostBent/KasamiAB.lean`.
It is specialized to the concrete field `GeneralizedKasami.GF n`, matching the
APN development in `RequestProject/KasamiAPN.lean`.

## Definitions

- `CollisionAnalysis.d k = 2^(2*k) - 2^k + 1` is the Kasami exponent.
- `KasamiAB.kasami_apn` is the APN interface: for every nonzero `a` and every
  `b`, the derivative fiber

  ```text
  { x | (x + a)^d + x^d = b }
  ```

  has cardinality at most two.
- `WalshAB.IsAB hcard f` says that every nonzero Walsh coefficient of `f` has
  squared value either `0` or `2^(n+1)`.

## APN Interface

`AlmostBent/KasamiAPNInterface.lean` imports `RequestProject.KasamiAPN` and
reuses

```lean
GeneralizedKasami.kasamiFunction_isAPN
```

for the concrete carrier `GF n`.  The interface converts the source theorem's
filtered-Finset fiber count into the subtype-cardinality statement expected by
the Walsh development using `Fintype.card_subtype`.  It also normalizes the two
syntactic forms of the Kasami exponent:

```text
4^k - 2^k + 1 = 2^(2*k) - 2^k + 1.
```

Thus `kasami_apn` is the bridge from the APN proof to the AB proof.

## Proof Sketch of the AB Property

The proof of `KasamiAB.kasami_is_ab` applies the general moment criterion
`WalshAB.ab_from_moments` to the Kasami power map.  This criterion combines
three inputs.

1. **Permutation / Parseval input.**

   `kasami_injective` proves that `x |-> x^d` is injective.  On the finite
   field, `kasami_bijective` turns injectivity into bijectivity.  The proof uses
   the exponent arithmetic and coprimality lemmas in `AlmostBent/CrossForm.lean`.

   Bijectivity supplies the Walsh Parseval identity through `parseval_perm`.

2. **APN fourth-moment input.**

   `kasami_is_apn_pred` applies `KasamiAPNInterface.kasami_apn` to obtain the
   differential fiber bound for the Kasami map.  Together with bijectivity,
   `fourth_moment_apn` gives the required fourth Walsh-moment identity.

3. **Walsh divisibility input.**

   `KasamiWalshDiv.kasami_walsh_div` proves the needed divisibility of each
   Walsh coefficient.  Its proof uses the quadratic substitution and the
   characteristic-two structure of the Kasami exponent.

The general theorem `ab_from_moments` combines Parseval, the APN fourth moment,
and coefficient divisibility.  Its integer-lattice argument forces each
nonzero Walsh coefficient to have the AB magnitude, yielding `IsAB` for the
Kasami monomial.

## Dependency Diagram

```text
RequestProject.KasamiAPN.kasamiFunction_isAPN
                    |
                    v
AlmostBent.KasamiAPNInterface.kasami_apn
                    |
                    v
KasamiAB.kasami_is_apn_pred -----> fourth_moment_apn
                    |
kasami_bijective ---> parseval_perm
                    |
KasamiWalshDiv.kasami_walsh_div
                    |
                    v
WalshAB.ab_from_moments
                    |
                    v
KasamiAB.kasami_is_ab
```

## Validation

The integrated target is built with:

```text
lake build AlmostBent.KasamiAB
```
