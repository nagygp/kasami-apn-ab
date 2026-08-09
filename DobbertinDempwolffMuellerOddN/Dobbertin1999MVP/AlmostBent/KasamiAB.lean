import Dobbertin1999MVP.AlmostBent.WalshLayers
import Dobbertin1999MVP.AlmostBent.CrossForm
import Dobbertin1999MVP.AlmostBent.WalshDiv
-------------------------------------------
-- Replace the following import with a
-- proper proof of the Kasami APN theorem
import Dobbertin1999MVP.AlmostBent.KasamiAPNInterface
-------------------------------------------

/-!
# Kasami Almost Bent (AB) Theorem

## Main Result

The Kasami power function `x ↦ x^d` with `d = 2^{2k} − 2^k + 1` is
**Almost Bent (AB)** on `GF(2ⁿ)` when `n` is odd, `gcd(k, n) = 1`, `k ≥ 1`.

## Proof Architecture

```
kasami_is_ab
  ├── ab_from_moments (WalshAB: integer lattice argument)
  │     ├── parseval_perm (Parseval identity)
  │     ├── fourth_moment_apn (Fourth moment for APN)
  │     └── kasami_walsh_div (Quadratic substitution divisibility)
  ├── kasami_is_apn_pred (CrossPairProof: Kasami is APN)
  └── kasami_bijective (Kasami is a permutation)
```
-/

set_option maxHeartbeats 800000

namespace KasamiAB

open Finset Fintype CollisionAnalysis WalshAB

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- The Kasami power map is injective (hence bijective on a finite set). -/
theorem kasami_injective {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : k ≥ 1) (hcop : Nat.Coprime k n) (hnodd : Odd n)
    (hn : 0 < n) : Function.Injective (fun x : F => x ^ d k) := by
  intro x y (hxy : x ^ d k = y ^ d k)
  by_cases hx : x = 0
  · subst hx
    rw [zero_pow (ne_of_gt (d_pos k hk))] at hxy
    by_contra hy
    exact (pow_ne_zero _ (Ne.symm hy)) hxy.symm
  · by_cases hy : y = 0
    · subst hy
      rw [zero_pow (ne_of_gt (d_pos k hk))] at hxy
      exact absurd hxy (pow_ne_zero _ hx)
    · exact pow_d_injective hcard k hk hcop hnodd hn x y hx hy hxy

/-- The Kasami power map is bijective on F. -/
theorem kasami_bijective {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : k ≥ 1) (hcop : Nat.Coprime k n) (hnodd : Odd n)
    (hn : 0 < n) : Function.Bijective (fun x : F => x ^ d k) :=
  (Finite.injective_iff_bijective).mp (kasami_injective hcard k hk hcop hnodd hn)

/-- Kasami is APN (reformulated using WalshAB.IsAPN). -/
theorem kasami_is_apn_pred {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : k ≥ 1) (hcop : Nat.Coprime k n) (hnodd : Odd n)
    (hn : n ≥ 1) (hkn : k < n) : IsAPN (fun x : F => x ^ d k) := by
  intro a ha b
  exact kasami_apn hk hn hkn hcop hnodd hcard a ha b


/-- **Kasami AB Theorem**: The Kasami power function `x^d` is Almost Bent.

Uses the quadratic substitution approach for Walsh divisibility
(`KasamiWalshDiv.kasami_walsh_div`), combined with the moment method
(`ab_from_moments`) from Nyberg's theorem. -/
theorem kasami_is_ab {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : k ≥ 1) (hcop : Nat.Coprime k n) (hnodd : Odd n)
  (hn : n ≥ 1) (hkn : k < n) : IsAB hcard (fun x : F => x ^ d k) := by
  apply ab_from_moments hcard _ hnodd hn
  · exact fun a ha => parseval_perm hcard _ (kasami_bijective hcard k hk hcop hnodd hn) a ha
  · exact fun a ha => fourth_moment_apn hcard (d k)
      (kasami_bijective hcard k hk hcop hnodd hn)
      (kasami_is_apn_pred hcard k hk hcop hnodd hn hkn) a ha
  · exact fun a b => KasamiWalshDiv.kasami_walsh_div hcard k hk hcop hnodd hn a b

end KasamiAB
