import AlmostBent.Defs
import RequestProject.KasamiAPN

/-!
# Kasami Almost Perfect Nonlinear (APN) Theorem

## Interface for the APN property for odd `n`

The Kasami power function `x ↦ x^d` with `d = 2^{2k} − 2^k + 1` is
**Almost Perfect Nonlinear (APN)** on `GF(2ⁿ)` when `gcd(k, n) = 1`, `k ≥ 1`.

Usage:

1. Copy the folder `WalshAB` in your project.
2. Replace sorry in the proof below.
3. Update the import paths to point to the copied `WalshAB` folder.

-/

set_option maxHeartbeats 800000

namespace KasamiAB

open Finset Fintype CollisionAnalysis

noncomputable section

local instance (n : ℕ) : DecidableEq (GeneralizedKasami.GF n) := Classical.decEq _
local instance (n : ℕ) : Fintype (GeneralizedKasami.GF n) := Fintype.ofFinite _

/-- **Kasami APN**: the Kasami power function `x^d` is APN. -/

theorem kasami_apn {k n : ℕ} (hk : k ≥ 1) (hkn : k < n)
    (hcop : Nat.Coprime k n) : ∀ a : GeneralizedKasami.GF n, a ≠ 0 → ∀ b : GeneralizedKasami.GF n,
      Fintype.card {x : GeneralizedKasami.GF n // (x + a) ^ d k + x ^ d k = b} ≤ 2 := by
  classical
  have h_apn := GeneralizedKasami.kasamiFunction_isAPN n k (by omega) (by omega) hkn hcop
  intro a ha b
  rw [Fintype.card_subtype]
  simpa [GeneralizedKasami.IsAPN, GeneralizedKasami.kasamiFunction,
    GeneralizedKasami.kasamiExponent, d, pow_two, pow_mul,
    show (4 : ℕ) = 2 ^ 2 by norm_num, add_comm] using h_apn a b ha

  end

end KasamiAB
