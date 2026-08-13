import Mathlib
import DobbDempMue.AlmostBent.WalshLayers
import DobbDempMue.AlmostBent.Defs

/-!
# Quadratic Gauss Sum Divisibility

For a quadratic function `Q : F → F` (vanishing third discrete derivative)
over `GF(2ⁿ)` with `n` odd, the character sum `∑_x χ(Q(x))` is divisible
by `2^{(n+1)/2}`.

## Proof strategy (S² factorization)

1. Expand `S² = ∑_{u,y} χ(Q(u+y) + Q(y))`.
2. Factor: `∑_y χ(Q(u+y)+Q(y)) = χ(Q(u)+Q(0)) · ∑_y χ(B(u,y))`
   where `B(u,·) = Q(u+·) + Q(u) + Q(·) + Q(0)` is additive.
3. Since `B(u,·)` is additive, `|F| ∣ ∑_y χ(B(u,y))`, hence `|F| ∣ S²`.
4. For odd `n`, the 2-adic valuation parity argument gives `2^{(n+1)/2} ∣ S`.
-/

set_option maxHeartbeats 1600000

namespace WalshDivisibility

open Finset Fintype BigOperators WalshAB CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## 2-adic valuation parity -/

/-- If `2^n ∣ S²` and `n` is odd, then `2^{(n+1)/2} ∣ S`. -/
theorem dvd_of_sq_dvd_pow_two_odd (S : ℤ) {n : ℕ} (_hodd : Odd n)
    (h : (2 : ℤ) ^ n ∣ S ^ 2) :
    (2 : ℤ) ^ ((n + 1) / 2) ∣ S := by
  contrapose! h
  rw [← Int.natAbs_dvd_natAbs, ← Nat.factorization_le_iff_dvd] <;> norm_num
  · exact lt_of_not_ge fun hn => h <| dvd_trans (pow_dvd_pow _ <| by omega) <|
      Int.natCast_pow 2 _ ▸ Int.natCast_dvd.mpr (Nat.ordProj_dvd _ _)
  · aesop

/-! ## Additive character sums -/

/-- For additive `g : F → F`, the sum `∑ y, χ(g(y))` is divisible by `|F|`. -/
theorem additive_char_sum_dvd (g : F → F)
    (hg_add : ∀ x y : F, g (x + y) = g x + g y) :
    (Fintype.card F : ℤ) ∣ ∑ y : F, χ (g y) := by
  by_cases h : ∀ y : F, Tr (g y) = 0 <;> simp_all +decide [χ]
  obtain ⟨a, ha⟩ := h
  have h_shift : ∑ x : F, χ (g x) = ∑ x : F, χ (g (x + a)) := by
    rw [← Equiv.sum_comp (Equiv.addRight a)]; aesop
  have h_neg : ∑ x : F, χ (g (x + a)) = -∑ x : F, χ (g x) := by
    simp +decide [← Finset.sum_neg_distrib, hg_add, χ_mul]
    exact Finset.sum_congr rfl fun x _ => by
      rw [show χ (g a) = -1 by exact if_neg ha]; ring
  have : ∑ x : F, χ (g x) = 0 := by grind +ring
  exact this.symm ▸ dvd_zero _

/-! ## Main theorem -/

/-- **Quadratic Gauss sum divisibility**: for a quadratic `Q : F → F`
(vanishing third derivative) over `GF(2ⁿ)` with `n` odd,
`2^{(n+1)/2} ∣ ∑_x χ(Q(x))`. -/
theorem quadratic_gauss_sum_div {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hodd : Odd n) (Q : F → F)
    (hQ_add3 : ∀ x y z : F,
      Q (x + y + z) + Q (x + y) + Q (x + z) + Q (y + z)
      + Q x + Q y + Q z + Q 0 = 0) :
    (2 : ℤ) ^ ((n + 1) / 2) ∣ ∑ x : F, χ (Q x) := by
  convert dvd_of_sq_dvd_pow_two_odd _ hodd _
  -- Expand S² = ∑_{u,y} χ(Q(u+y) + Q(y))
  have h_expand : (∑ x : F, χ (Q x)) ^ 2 =
      ∑ u : F, ∑ y : F, χ (Q (u + y) + Q y) := by
    rw [sq, ← Finset.sum_comm]
    simp +decide only [Finset.mul_sum _ _ _, mul_comm, χ_mul]
    exact Finset.sum_congr rfl fun x _ => by
      rw [← Equiv.sum_comp (Equiv.addRight x)]; simp +decide
  -- Factor: ∑_y χ(Q(u+y)+Q(y)) = χ(Q(u)+Q(0)) · ∑_y χ(B(u,y))
  have h_factor : ∀ u : F, ∑ y : F, χ (Q (u + y) + Q y) =
      χ (Q u + Q 0) * ∑ y : F, χ (Q (u + y) + Q u + Q y + Q 0) := by
    intro u; rw [Finset.mul_sum _ _ _]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp +decide [χ_mul]; ring_nf; simp +decide [χ_sq]
  -- B(u,·) is additive ⟹ |F| divides its character sum
  have h_div : ∀ u : F, (Fintype.card F : ℤ) ∣
      ∑ y : F, χ (Q (u + y) + Q u + Q y + Q 0) := by
    intro u
    apply additive_char_sum_dvd
    intro x y
    have := hQ_add3 u x y
    simp_all +decide [add_assoc]
    grind +ring
  simp_all +decide
  exact Finset.dvd_sum fun x _ => dvd_mul_of_dvd_right (h_div x) _

end WalshDivisibility
