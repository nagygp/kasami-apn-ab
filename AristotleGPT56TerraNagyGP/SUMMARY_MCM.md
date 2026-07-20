# Summary of MCM permutation corollary

Added `mcm_isPermutation` to `RequestProject/genMCM.lean`.

The theorem formalizes the Muller--Cohen--Matthews permutation-polynomial
corollary:

- `n` and `k` are positive natural numbers;
- `k < n` and `Nat.Coprime k n`;
- `k` is odd, expressed as `k % 2 = 1`;
- the conclusion is `IsPermutationPolynomial (genMCMpol n k 0)` over
  `GF(2^n)`.

The proof specializes `dobbertin_theorem4` to `beta = 0`. It obtains a
representative `kInv` for the inverse of `k` modulo `n`, defines `nPrime` by
`kInv * k = nPrime * n + 1`, and chooses the Theorem 4 parameter
`a = nPrime mod 2`. The oddness of `k` proves the two required parity
conditions:

- `kInv + a * n` is odd;
- `0 = nPrime + a * k (mod 2)`.

Applying `dobbertin_theorem4` then yields the required permutation result for
`genMCMpol n k 0`.

Verification completed successfully with:

```text
lake env lean RequestProject/genMCM.lean
lake build
```

The new theorem contains no `sorry` or `admit`.
