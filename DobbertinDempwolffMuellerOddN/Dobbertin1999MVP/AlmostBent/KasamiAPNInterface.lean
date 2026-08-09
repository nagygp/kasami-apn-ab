import Dobbertin1999MVP.AlmostBent.Defs
import Dobbertin1999MVP.Dobbertin1999.APN

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
theorem kasami_apn {k n : ℕ} (hk : k ≥ 1) (hn : n ≥ 1) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n)
    (hcard : Fintype.card F = 2 ^ n) :
    ∀ a : F, a ≠ 0 → ∀ b : F,
      Fintype.card {x : F // (x + a) ^ d k + x ^ d k = b} ≤ 2 := by
  intro a ha b
  rcases Dobbertin1999.APN.kasami_is_apn_solution_count hcard k hk hkn hnodd hcop a ha b with h | h
  · have h' : Nat.card {x : F // (x + a) ^ d k + x ^ d k = b} = 0 := by
      simpa only [d, Dobbertin1999.MCMtoAPN.kasamiExp, KasamiAPN.kasamiExp] using h
    rw [← Nat.card_eq_fintype_card, h']
    omega
  · have h' : Nat.card {x : F // (x + a) ^ d k + x ^ d k = b} = 2 := by
      simpa only [d, Dobbertin1999.MCMtoAPN.kasamiExp, KasamiAPN.kasamiExp] using h
    rw [← Nat.card_eq_fintype_card, h']

end KasamiAB
