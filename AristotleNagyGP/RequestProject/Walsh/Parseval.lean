import RequestProject.Walsh.AB

/-!
# Parseval identity for the Walsh transform

For a permutation `f : GF(2^n) → GF(2^n)`, the second moment of its Walsh
spectrum satisfies `∑_b W_f(a,b)^2 = 2^{2n}` for every `a`.
-/

open scoped BigOperators
open Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace GeneralizedKasami

/-- Orthogonality, summed over the *left* factor. -/
lemma signChar_orthogonality' (n : ℕ) (hn : 0 < n) (c : GF n) :
    (∑ b : GF n, signChar n (b * c)) = if c = 0 then (2 ^ n : ℤ) else 0 := by
  rw [← signChar_orthogonality n hn c]
  apply Finset.sum_congr rfl
  intro b _
  rw [mul_comm]

/-- Expansion of the square of a Walsh coefficient as a double sum. -/
lemma walsh_sq_expand (n : ℕ) (hn : 0 < n) (f : GF n → GF n) (a b : GF n) :
    (walsh n f a b) ^ 2 =
      ∑ x : GF n, ∑ y : GF n, signChar n (a * (x + y) + b * (f x + f y)) := by
  unfold walsh
  rw [sq, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [← signChar_add n hn]
  congr 1
  ring

/-- Summing the squared Walsh coefficient over `b` collapses via orthogonality. -/
lemma sum_walsh_sq_eq (n : ℕ) (hn : 0 < n) (f : GF n → GF n) (a : GF n) :
    (∑ b : GF n, (walsh n f a b) ^ 2) =
      ∑ x : GF n, ∑ y : GF n,
        signChar n (a * (x + y)) * (if f x + f y = 0 then (2 ^ n : ℤ) else 0) := by
  simp_rw [walsh_sq_expand n hn f a]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  -- ∑_b signChar(a(x+y) + b(fx+fy)) = signChar(a(x+y)) * (∑_b signChar(b(fx+fy)))
  rw [← signChar_orthogonality' n hn (f x + f y)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [← signChar_add n hn]

/-- **Parseval identity.**  For a permutation `f`, the second Walsh moment is
`2^{2n}`. -/
theorem walsh_parseval (n : ℕ) (hn : 0 < n) (f : GF n → GF n)
    (hf : Function.Bijective f) (a : GF n) :
    (∑ b : GF n, (walsh n f a b) ^ 2) = 2 ^ (2 * n) := by
  rw [sum_walsh_sq_eq n hn f a]
  -- f x + f y = 0 ↔ x = y (injective, char two)
  have hchar : ∀ x y : GF n, (f x + f y = 0) ↔ x = y := by
    intro x y
    haveI := Fact.mk (show Nat.Prime 2 by decide)
    rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq]
    exact ⟨fun h => hf.1 h, fun h => by rw [h]⟩
  -- inner: for each x, only y = x contributes 2^n, giving ∑_x 2^n = 2^{2n}
  have hinner : ∀ x : GF n,
      (∑ y : GF n, signChar n (a * (x + y)) * (if f x + f y = 0 then (2 ^ n : ℤ) else 0))
        = 2 ^ n := by
    intro x
    rw [Finset.sum_eq_single x]
    · rw [if_pos (by simp [CharTwo.add_self_eq_zero])]
      simp [CharTwo.add_self_eq_zero]
    · intro y _ hyx
      rw [if_neg (fun h => hyx (((hchar x y).mp h).symm))]
      ring
    · intro h; exact absurd (Finset.mem_univ x) h
  rw [Finset.sum_congr rfl (fun x _ => hinner x)]
  rw [Finset.sum_const, Finset.card_univ, card_GF n hn]
  rw [nsmul_eq_mul]
  push_cast
  rw [← pow_add]
  congr 1
  omega

end GeneralizedKasami
