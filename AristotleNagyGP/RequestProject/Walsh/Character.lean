import RequestProject.basic

/-!
# Sign character and orthogonality on `GF(2^n)`

This file develops the additive sign character
`χ(z) = (-1)^{Tr(z)}` on `GF(2^n)`, where `Tr` is the absolute trace
`Tr(z) = ∑_{i<n} z^{2^i}`, together with the fundamental orthogonality relation.
These are the analytic foundations of the Walsh transform used to prove the
Almost Bent property of the Kasami function.
-/

open scoped BigOperators
open Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace GeneralizedKasami

/-- The absolute trace `Tr(z) = ∑_{i<n} z^{2^i}` as an element of `GF(2^n)`.
Its values lie in the prime subfield `{0,1}`. -/
noncomputable def absTr (n : ℕ) (z : GF n) : GF n :=
  ∑ i ∈ Finset.range n, z ^ (2 ^ i)

/-- The sign character `χ(z) = (-1)^{Tr(z)}`, valued in `{1,-1} ⊆ ℤ`. -/
noncomputable def signChar (n : ℕ) (z : GF n) : ℤ :=
  if absTr n z = 0 then 1 else -1

/-- `GF(2^n)` is a finite type. -/
noncomputable instance instFintypeGF (n : ℕ) : Fintype (GF n) := Fintype.ofFinite _

/-- The cardinality of `GF(2^n)`. -/
lemma card_GF (n : ℕ) (hn : 0 < n) : Fintype.card (GF n) = 2 ^ n := by
  have h := GaloisField.card 2 n (by omega)
  rw [Nat.card_eq_fintype_card] at h
  exact h

/-- The absolute trace is additive. -/
lemma absTr_add (n : ℕ) (x y : GF n) : absTr n (x + y) = absTr n x + absTr n y := by
  unfold absTr
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  haveI := Fact.mk (show Nat.Prime 2 by decide)
  rw [add_pow_char_pow]

/-- `Tr(z)` is fixed by squaring, hence lies in `{0,1}`. -/
lemma absTr_sq (n : ℕ) (hn : 0 < n) (z : GF n) : (absTr n z) ^ 2 = absTr n z := by
  simpa using trace_sum_frobenius n 1 z hn

/-- The absolute trace takes values in `{0,1}`. -/
lemma absTr_mem (n : ℕ) (hn : 0 < n) (z : GF n) : absTr n z = 0 ∨ absTr n z = 1 := by
  have h := absTr_sq n hn z
  have : absTr n z * (absTr n z - 1) = 0 := by ring_nf; linear_combination h
  rcases mul_eq_zero.mp this with h0 | h1
  · left; exact h0
  · right; linear_combination h1

@[simp] lemma signChar_zero (n : ℕ) : signChar n 0 = 1 := by
  unfold signChar absTr; simp

/-- The sign character is multiplicative with respect to addition. -/
lemma signChar_add (n : ℕ) (hn : 0 < n) (x y : GF n) :
    signChar n (x + y) = signChar n x * signChar n y := by
  unfold signChar
  rw [absTr_add]
  rcases absTr_mem n hn x with hx | hx <;> rcases absTr_mem n hn y with hy | hy <;>
    simp only [hx, hy]
  · simp
  · simp
  · simp
  · -- 1 + 1 = 0 in characteristic two
    haveI := Fact.mk (show Nat.Prime 2 by decide)
    have h2 : (1 : GF n) + 1 = 0 := by
      have := CharTwo.add_self_eq_zero (1 : GF n); simpa using this
    rw [h2]; simp

/-- The sign character values are `±1`. -/
lemma signChar_sq (n : ℕ) (z : GF n) : (signChar n z) ^ 2 = 1 := by
  unfold signChar; split <;> ring

/-- The absolute trace is not identically zero (`n ≥ 1`). -/
lemma exists_absTr_ne_zero (n : ℕ) (hn : 0 < n) : ∃ z : GF n, absTr n z ≠ 0 := by
  by_cases hn_odd : n % 2 = 1
  · -- When n is odd, absTr n 1 = n = 1 mod 2 = 1
    use 1
    rw [absTr]
    simp [Finset.sum_const, Finset.card_range]
    norm_cast
    intro h
    have hdiv : 2 ∣ n := by
      have := CharP.cast_eq_zero_iff (GF n) 2
      rw [this] at h
      exact h
    omega
  · -- When n is even, the trace polynomial is nonzero and has degree < |GF(2^n)|
    -- So it can't vanish on all elements
    by_contra hall
    push_neg at hall
    -- hall : ∀ z, absTr n z = 0
    -- Consider the trace polynomial T(X) = ∑_{i<n} X^(2^i)
    -- If T vanishes on all elements of GF(2^n), then T has 2^n roots
    -- But deg(T) = 2^(n-1) < 2^n, contradiction
    have hcard : Fintype.card (GF n) = 2 ^ n := card_GF n hn
    -- The trace polynomial has degree 2^(n-1) when n ≥ 1
    have hdeg : (tracePolynomial n).natDegree < 2 ^ n := by
      rw [tracePolynomial]
      have hle : (∑ i ∈ Finset.range n, (Polynomial.X : Polynomial (GF n)) ^ (2 : ℕ) ^ i).natDegree ≤ 2 ^ (n - 1) := by
        refine Polynomial.natDegree_sum_le_of_forall_le (Finset.range n) (fun i => Polynomial.X ^ (2 ^ i)) ?_
        intro i hi
        rw [Polynomial.natDegree_X_pow]
        exact pow_le_pow_right₀ (by decide : 1 ≤ 2) (Nat.le_pred_of_lt (Finset.mem_range.mp hi))
      exact lt_of_le_of_lt hle (pow_lt_pow_right₀ (by decide : 1 < 2) (Nat.sub_lt hn (by decide)))
    -- If hall holds, then tracePolynomial n vanishes on all elements
    have hroots : ∀ z : GF n, (tracePolynomial n).eval z = 0 := by
      intro z
      simp only [tracePolynomial, Polynomial.eval_finset_sum, Polynomial.eval_pow, Polynomial.eval_X]
      exact hall z
    -- A nonzero polynomial of degree d has at most d roots
    -- But we have 2^n roots and degree < 2^n, contradiction
    have hn2 : 1 < n := by omega
    have hne : tracePolynomial n ≠ 0 := by
      show ¬ (∑ i ∈ Finset.range n, Polynomial.X ^ (2 : ℕ) ^ i : Polynomial (GF n)) = 0
      intro hzero
      have h0 : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.mpr hn
      have hcoeff := congr_arg (fun p => p.coeff 1) hzero
      simp [Polynomial.coeff_X_pow] at hcoeff
      rw [show (Finset.range n).filter (fun x => 1 = 2 ^ x) = {0} from ?_] at hcoeff
      · simp at hcoeff
      · ext x
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        constructor
        · intro ⟨hx_range, hx_eq⟩
          rw [eq_comm] at hx_eq
          have := Nat.pow_eq_one.mp hx_eq
          simp at this
          exact this
        · intro hx
          rw [hx]
          exact ⟨hn, by norm_num⟩
    have hcard_roots : (tracePolynomial n).roots.toFinset.card ≤ (tracePolynomial n).natDegree := by
      exact le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' (tracePolynomial n))
    have hall_roots : (tracePolynomial n).roots.toFinset = Finset.univ := by
      ext z
      simp [Polynomial.mem_roots hne, hroots z]
    rw [hall_roots, Finset.card_univ] at hcard_roots
    rw [hcard] at hcard_roots
    linarith

/-- **Orthogonality of the sign character.**  For every `c : GF(2^n)`,
`∑_x χ(c·x) = 2^n` if `c = 0`, and `0` otherwise. -/
theorem signChar_orthogonality (n : ℕ) (hn : 0 < n) (c : GF n) :
    (∑ x : GF n, signChar n (c * x)) = if c = 0 then (2 ^ n : ℤ) else 0 := by
  by_cases hc : c = 0
  · subst hc
    simp only [zero_mul, signChar_zero]
    rw [Finset.sum_const, Finset.card_univ, card_GF n hn]
    simp
  · rw [if_neg hc]
    -- The standard translation trick: find x₀ with χ(c·x₀) = -1, then
    -- x ↦ x + x₀ negates every summand while permuting the sum.
    obtain ⟨z, hz⟩ := exists_absTr_ne_zero n hn
    set x0 : GF n := c⁻¹ * z with hx0
    have hcx0 : c * x0 = z := by
      rw [hx0, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    have hsign : signChar n (c * x0) = -1 := by
      rw [hcx0]; unfold signChar; rw [if_neg hz]
    have hreindex : (∑ x : GF n, signChar n (c * (x + x0))) = ∑ x : GF n, signChar n (c * x) :=
      Equiv.sum_comp (Equiv.addRight x0) (fun x => signChar n (c * x))
    have hstep : (∑ x : GF n, signChar n (c * (x + x0)))
        = - (∑ x : GF n, signChar n (c * x)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro x _
      rw [mul_add, signChar_add n hn, hsign]
      ring
    rw [hreindex] at hstep
    linarith [hstep]

end GeneralizedKasami
