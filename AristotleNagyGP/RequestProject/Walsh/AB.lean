import RequestProject.Walsh.Character

/-!
# The Walsh transform and the Almost Bent property

This file defines the Walsh transform of a function `f : GF(2^n) → GF(2^n)`,
the Almost Bent predicate `IsAB`, and the abstract moment criterion
`ab_from_moments`: a function whose Walsh spectrum satisfies the Parseval
identity, the fourth-moment identity, and the `2^{(n+1)/2}`-divisibility bound
is Almost Bent.
-/

open scoped BigOperators
open Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace GeneralizedKasami

/-- The Walsh transform coefficient of `f` at `(a,b)`:
`W_f(a,b) = ∑_x χ(a·x + b·f(x))`. -/
noncomputable def walsh (n : ℕ) (f : GF n → GF n) (a b : GF n) : ℤ :=
  ∑ x : GF n, signChar n (a * x + b * f x)

/-- **Almost Bent.**  For every nonzero shift `a`, every squared Walsh
coefficient is either `0` or `2^{n+1}`. -/
def IsAB (n : ℕ) (f : GF n → GF n) : Prop :=
  ∀ a : GF n, a ≠ 0 → ∀ b : GF n,
    (walsh n f a b) ^ 2 = 0 ∨ (walsh n f a b) ^ 2 = 2 ^ (n + 1)

/-- Integer-lattice core: if `∑ k_i^2 = ∑ k_i^4` (a common value `M`), then
every `k_i^2 ∈ {0,1}`. -/
lemma sq_mem_of_sum_sq_eq_sum_pow4 {ι : Type*} [Fintype ι] (k : ι → ℤ) (M : ℤ)
    (h2 : ∑ i, (k i) ^ 2 = M) (h4 : ∑ i, (k i) ^ 4 = M) :
    ∀ i, (k i) ^ 2 = 0 ∨ (k i) ^ 2 = 1 := by
  -- ∑ (k_i^4 - k_i^2) = 0, each term ≥ 0, so each term = 0
  have hsum : ∑ i, ((k i) ^ 4 - (k i) ^ 2) = 0 := by
    rw [Finset.sum_sub_distrib, h4, h2, sub_self]
  have hnonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ (k i) ^ 4 - (k i) ^ 2 := by
    intro i _
    have : (k i) ^ 4 - (k i) ^ 2 = (k i) ^ 2 * ((k i) ^ 2 - 1) := by ring
    rw [this]
    rcases le_or_gt ((k i) ^ 2) 0 with h | h
    · have : (k i) ^ 2 = 0 := le_antisymm h (sq_nonneg _)
      simp [this]
    · have h1 : 1 ≤ (k i) ^ 2 := by
        have : (k i) ^ 2 ≠ 0 := ne_of_gt h
        nlinarith [sq_nonneg (k i)]
      nlinarith
  intro i
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum i (Finset.mem_univ i)
  have : (k i) ^ 2 * ((k i) ^ 2 - 1) = 0 := by nlinarith [hzero]
  rcases mul_eq_zero.mp this with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linarith)

/-- **The abstract AB criterion (`ab_from_moments`).**  A function whose Walsh
spectrum satisfies the Parseval identity, the fourth-moment identity, and the
`2^{(n+1)/2}`-divisibility bound is Almost Bent. -/
theorem ab_from_moments (n : ℕ) (hn : 0 < n) (hodd : Odd n) (f : GF n → GF n)
    (hParseval : ∀ a : GF n, a ≠ 0 → (∑ b : GF n, (walsh n f a b) ^ 2) = 2 ^ (2 * n))
    (hFourth : ∀ a : GF n, a ≠ 0 → (∑ b : GF n, (walsh n f a b) ^ 4) = 2 * 2 ^ (3 * n))
    (hDiv : ∀ a : GF n, a ≠ 0 → ∀ b : GF n, (2 : ℤ) ^ ((n + 1) / 2) ∣ walsh n f a b) :
    IsAB n f := by
  intro a ha b
  set m := (n + 1) / 2 with hm
  have h2m : 2 * m = n + 1 := by
    obtain ⟨t, ht⟩ := hodd
    omega
  -- write each Walsh coefficient as 2^m * k b
  choose k hk using hDiv a ha
  -- Parseval in terms of k : ∑ (k b)^2 = 2^(n-1)
  have hpar : (∑ b : GF n, (k b) ^ 2) = 2 ^ (n - 1) := by
    have hexp : (∑ b : GF n, (walsh n f a b) ^ 2) = 2 ^ (n + 1) * (∑ b : GF n, (k b) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [hk b, mul_pow, ← pow_mul, mul_comm m 2, h2m]
    rw [hParseval a ha] at hexp
    have hsplit : (2 : ℤ) ^ (2 * n) = 2 ^ (n + 1) * 2 ^ (n - 1) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit] at hexp
    have hne : (2 : ℤ) ^ (n + 1) ≠ 0 := by positivity
    exact (mul_right_cancel₀ hne (by linarith [hexp])).symm
  -- fourth moment in terms of k : ∑ (k b)^4 = 2^(n-1)
  have hfour : (∑ b : GF n, (k b) ^ 4) = 2 ^ (n - 1) := by
    have hexp : (∑ b : GF n, (walsh n f a b) ^ 4) = 2 ^ (2 * (n + 1)) * (∑ b : GF n, (k b) ^ 4) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [hk b, mul_pow, ← pow_mul]
      congr 2
      omega
    rw [hFourth a ha] at hexp
    have hsplit : (2 : ℤ) * 2 ^ (3 * n) = 2 ^ (2 * (n + 1)) * 2 ^ (n - 1) := by
      rw [← pow_succ', ← pow_add]; congr 1; omega
    rw [hsplit] at hexp
    have hne : (2 : ℤ) ^ (2 * (n + 1)) ≠ 0 := by positivity
    exact (mul_right_cancel₀ hne (by linarith [hexp])).symm
  have hkey := sq_mem_of_sum_sq_eq_sum_pow4 k (2 ^ (n - 1)) hpar hfour b
  have hwb : walsh n f a b = 2 ^ m * k b := hk b
  rcases hkey with h0 | h1
  · left
    rw [hwb]; rw [mul_pow]
    have : (k b) ^ 2 = 0 := h0
    rw [this]; ring
  · right
    rw [hwb, mul_pow, h1, mul_one, ← pow_mul, mul_comm m 2, h2m]

end GeneralizedKasami
