# Summary of Kasami APN formalization

Created `RequestProject/KasamiAPN.lean`, formalizing the APN property of the
Kasami monomial over `GF(2^n)`.

## Definitions

- `kasamiExponent k = 4^k - 2^k + 1`
- `kasamiFunction n k x = x ^ kasamiExponent k`
- `IsAPN n f`: for every nonzero difference `a` and every target `b`, the
  fiber of `x |-> f x + f (x + a)` above `b` has cardinality at most two.
- `IsTwoToOne n g`: every fiber of `g` has cardinality at most two.
- `kasamiNormalizedDerivative n k x = kasamiFunction n k x +
  kasamiFunction n k (x + 1) + 1`.

## Formalized proof steps

1. **Complementary exponents.**
   `kasamiExponent_complement_identity` proves

   ```text
   d(n-k) * 2^(2*k) = d(k) + (2^n - 1) * (2^n + 1 - 2^k).
   ```

   `kasamiFunction_complement_frobenius` uses finite-field exponent reduction
   to show that `kasamiFunction n k` is the `2^(2*k)`-th Frobenius power of
   `kasamiFunction n (n-k)`.

2. **Complementary APN equivalence.**
   `frobeniusPower_injective` and `isAPN_frobeniusPower_iff` show that
   postcomposition by a Frobenius power preserves APN.  Consequently,
   `kasamiFunction_isAPN_iff_complement` proves that the Kasami functions with
   parameters `k` and `n-k` are APN simultaneously.

3. **Normalized derivative criterion.**
   `kasami_derivative_scale_iff` normalizes a derivative with nonzero
   difference `a` using the change of variables `x = a*y`.
   `kasamiFunction_isAPN_iff_normalizedDerivative_twoToOne` proves

   ```text
   IsAPN n (kasamiFunction n k) <->
     IsTwoToOne n (kasamiNormalizedDerivative n k).
   ```

4. **MCM identity.**
   `mcm_sum_at_quadratic` telescopes the MCM numerator at `x + x^2`.
   `kasami_normalizedDerivative_mul_quadratic_pow` proves the
   denominator-cleared identity.  Together they yield
   `kasamiNormalizedDerivative_eq_genMCMeval`:

   ```text
   kasamiNormalizedDerivative n k x =
     genMCMeval n k 0 (x + x^2).
   ```

5. **Odd parameter.**
   `quadratic_collision` and `quadratic_isTwoToOne` prove that
   `x |-> x + x^2` has fibers of cardinality at most two.  Combining this with
   the MCM permutation theorem `mcm_isPermutation` gives
   `kasamiFunction_isAPN_of_odd` for odd `k` coprime to `n`.

6. **Even parameter.**
   `kasamiFunction_isAPN_of_even` proves that if `k` is even and coprime to
   `n`, then `n` is odd and `n-k` is odd.  The odd result for `n-k`, together
   with the complementary APN equivalence, proves APN for `k`.

## Final theorem

```lean
theorem kasamiFunction_isAPN
    (n k : ℕ)
    (hn : 0 < n) (hk : 0 < k) (hkn : k < n)
    (hcop : Nat.Coprime k n) :
    IsAPN n (kasamiFunction n k)
```

The theorem splits on the parity of `k` and applies the odd or even result.

## Validation

Both commands complete successfully:

```text
lake env lean RequestProject/KasamiAPN.lean
lake build
```
