import AlmostBent.Defs

/-!
# Kasami Almost Perfect Nonlinear (APN) Theorem

## Interface for the APN property for odd `n`

The Kasami power function `x ↦ x^d` with `d = 2^{2k} − 2^k + 1` is
**Almost Perfect Nonlinear (APN)** on `GF(2ⁿ)` when `gcd(k, n) = 1`, `k ≥ 1`.

-/

set_option maxHeartbeats 800000

namespace KasamiAB

open Finset Fintype CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **Kasami APN**: the Kasami power function `x^d` is APN. -/
theorem kasami_apn {k n : ℕ} (hk : k ≥ 1) (hn : n ≥ 1)
    (hcop : Nat.Coprime k n) (hnodd : Odd n)
    (hcard : Fintype.card F = 2 ^ n) :
    ∀ a : F, a ≠ 0 → ∀ b : F,
      Fintype.card {x : F // (x + a) ^ d k + x ^ d k = b} ≤ 2 := by
  sorry

end KasamiAB
