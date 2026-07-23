import RequestProject.Walsh.Parseval
import RequestProject.KasamiAPN

/-!
# Fourth moment of the Walsh spectrum from APN

For a permutation monomial `f(x) = x^d` on `GF(2^n)` that is APN, the fourth
moment of its Walsh spectrum satisfies `∑_b W_f(a,b)^4 = 2·2^{3n}` for every
nonzero `a`.

The proof reduces the fourth moment to a weighted count `Sfour` of quadruples
`(x1,x2,x3,x4)` with `∑ x_i^d = 0`, and evaluates that count using:

* the total number of such quadruples (`S1count = 2^{3n}`, from bijectivity);
* the number of them additionally satisfying `∑ x_i = 0` (`S0count = 3·2^{2n} - 2·2^n`,
  from APN);
* a scaling/character reindexing identity relating `Sfour`, `S0count`, `S1count`.
-/

open scoped BigOperators
open Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace GeneralizedKasami

/-- The weighted quadruple sum `Sfour(a) = ∑_{∑ xᵢ^d = 0} χ(a·∑ xᵢ)`. -/
noncomputable def Sfour (n d : ℕ) (a : GF n) : ℤ :=
  ∑ x1 : GF n, ∑ x2 : GF n, ∑ x3 : GF n, ∑ x4 : GF n,
    (if x1 ^ d + x2 ^ d + x3 ^ d + x4 ^ d = 0 then signChar n (a * (x1 + x2 + x3 + x4)) else 0)

/-- The scaled variant `A(a,t) = ∑_{∑ xᵢ^d=0} χ(a·t·∑ xᵢ)`. -/
noncomputable def Afun (n d : ℕ) (a t : GF n) : ℤ :=
  ∑ x1 : GF n, ∑ x2 : GF n, ∑ x3 : GF n, ∑ x4 : GF n,
    (if x1 ^ d + x2 ^ d + x3 ^ d + x4 ^ d = 0 then signChar n (a * t * (x1 + x2 + x3 + x4)) else 0)

/-- Number of quadruples with `∑ xᵢ^d = 0`. -/
noncomputable def S1count (n d : ℕ) : ℤ :=
  ∑ x1 : GF n, ∑ x2 : GF n, ∑ x3 : GF n, ∑ x4 : GF n,
    (if x1 ^ d + x2 ^ d + x3 ^ d + x4 ^ d = 0 then (1 : ℤ) else 0)

/-- Number of quadruples with `∑ xᵢ = 0` and `∑ xᵢ^d = 0`. -/
noncomputable def S0count (n d : ℕ) : ℤ :=
  ∑ x1 : GF n, ∑ x2 : GF n, ∑ x3 : GF n, ∑ x4 : GF n,
    (if x1 + x2 + x3 + x4 = 0 ∧ x1 ^ d + x2 ^ d + x3 ^ d + x4 ^ d = 0 then (1 : ℤ) else 0)

/-- Expansion of the fourth Walsh moment as `2^n · Sfour`. -/
lemma sum_walsh_fourth_eq_Sfour (n d : ℕ) (hn : 0 < n) (a : GF n) :
    (∑ b : GF n, (walsh n (fun x => x ^ d) a b) ^ 4) = 2 ^ n * Sfour n d a := by
  have hexp : ∀ b : GF n, (walsh n (fun x => x ^ d) a b) ^ 4
      = ∑ x1 : GF n, ∑ x2 : GF n, ∑ x3 : GF n, ∑ x4 : GF n,
          signChar n (a * (x1 + x2 + x3 + x4) + b * (x1 ^ d + x2 ^ d + x3 ^ d + x4 ^ d)) := by
    intro b
    unfold walsh
    dsimp only
    have hpow : (∑ x : GF n, signChar n (a * x + b * x ^ d)) ^ 4
        = ∑ x1 : GF n, ∑ x2 : GF n, ∑ x3 : GF n, ∑ x4 : GF n,
            signChar n (a * x1 + b * x1 ^ d) * signChar n (a * x2 + b * x2 ^ d)
              * signChar n (a * x3 + b * x3 ^ d) * signChar n (a * x4 + b * x4 ^ d) := by
      have e : (∑ x : GF n, signChar n (a * x + b * x ^ d)) ^ 4
          = (∑ x1 : GF n, signChar n (a * x1 + b * x1 ^ d))
            * ((∑ x2 : GF n, signChar n (a * x2 + b * x2 ^ d))
            * ((∑ x3 : GF n, signChar n (a * x3 + b * x3 ^ d))
            * (∑ x4 : GF n, signChar n (a * x4 + b * x4 ^ d)))) := by ring
      rw [e]; simp only [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ =>
        Finset.sum_congr rfl (fun x3 _ => Finset.sum_congr rfl (fun x4 _ => by ring))))
    rw [hpow]
    refine Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ =>
      Finset.sum_congr rfl (fun x3 _ => Finset.sum_congr rfl (fun x4 _ => ?_))))
    rw [← signChar_add n hn, ← signChar_add n hn, ← signChar_add n hn]
    congr 1; ring
  have key : ∀ x1 x2 x3 x4 : GF n,
      (∑ b : GF n, signChar n (a * (x1 + x2 + x3 + x4) + b * (x1 ^ d + x2 ^ d + x3 ^ d + x4 ^ d)))
      = (if x1 ^ d + x2 ^ d + x3 ^ d + x4 ^ d = 0
          then 2 ^ n * signChar n (a * (x1 + x2 + x3 + x4)) else 0) := by
    intro x1 x2 x3 x4
    have hsplit : (∑ b : GF n, signChar n (a * (x1 + x2 + x3 + x4) + b * (x1 ^ d + x2 ^ d + x3 ^ d + x4 ^ d)))
        = signChar n (a * (x1 + x2 + x3 + x4))
          * ∑ b : GF n, signChar n (b * (x1 ^ d + x2 ^ d + x3 ^ d + x4 ^ d)) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; rw [← signChar_add n hn]
    rw [hsplit, signChar_orthogonality' n hn]
    by_cases h : x1 ^ d + x2 ^ d + x3 ^ d + x4 ^ d = 0
    · simp [h]; ring
    · simp [h]
  simp_rw [hexp]
  unfold Sfour
  rw [Finset.mul_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x1 _
  rw [Finset.mul_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x2 _
  rw [Finset.mul_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x3 _
  rw [Finset.mul_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x4 _
  rw [key x1 x2 x3 x4]
  by_cases h : x1 ^ d + x2 ^ d + x3 ^ d + x4 ^ d = 0 <;> simp [h]

/-- `Sfour(a) = Afun(a,1)`. -/
lemma Sfour_eq_Afun_one (n d : ℕ) (a : GF n) : Sfour n d a = Afun n d a 1 := by
  unfold Sfour Afun; simp

/-- Scaling reindex: for `t ≠ 0`, `Afun(a,t) = Sfour(a)`. -/
lemma Afun_eq_Sfour (n d : ℕ) (a t : GF n) (ht : t ≠ 0) :
    Afun n d a t = Sfour n d a := by
  unfold Afun Sfour
  let e : GF n ≃ GF n := {
    toFun := fun x => t * x
    invFun := fun x => t⁻¹ * x
    left_inv := fun x => by simp [ht]
    right_inv := fun x => by simp [ht]
  }
  -- Use the bijection y = t * x to reindex the LHS
  have h : ∀ f : GF n → ℤ, (∑ x, f x) = ∑ y, f (t⁻¹ * y) := by
    intro f
    rw [← e.symm.sum_comp f]
    rfl
  calc (∑ x1, ∑ x2, ∑ x3, ∑ x4,
        if x1^d + x2^d + x3^d + x4^d = 0 
          then signChar n (a * t * (x1 + x2 + x3 + x4)) else 0)
      = ∑ y1, ∑ x2, ∑ x3, ∑ x4,
          if (t⁻¹ * y1)^d + x2^d + x3^d + x4^d = 0 
            then signChar n (a * t * (t⁻¹ * y1 + x2 + x3 + x4)) else 0 := by rw [h]
    _ = ∑ y1, ∑ y2, ∑ x3, ∑ x4,
          if (t⁻¹ * y1)^d + (t⁻¹ * y2)^d + x3^d + x4^d = 0 
            then signChar n (a * t * (t⁻¹ * y1 + t⁻¹ * y2 + x3 + x4)) else 0 := by
        congr 1; ext y1; rw [h]
    _ = ∑ y1, ∑ y2, ∑ y3, ∑ x4,
          if (t⁻¹ * y1)^d + (t⁻¹ * y2)^d + (t⁻¹ * y3)^d + x4^d = 0 
            then signChar n (a * t * (t⁻¹ * y1 + t⁻¹ * y2 + t⁻¹ * y3 + x4)) else 0 := by
        congr 2; ext y1; congr 2; ext y2; rw [h]
    _ = ∑ y1, ∑ y2, ∑ y3, ∑ y4,
          if (t⁻¹ * y1)^d + (t⁻¹ * y2)^d + (t⁻¹ * y3)^d + (t⁻¹ * y4)^d = 0 
            then signChar n (a * t * (t⁻¹ * y1 + t⁻¹ * y2 + t⁻¹ * y3 + t⁻¹ * y4)) else 0 := by
        congr 3; ext y1; congr 3; ext y2; congr 3; ext y3; rw [h]
    _ = ∑ x1, ∑ x2, ∑ x3, ∑ x4,
          if x1^d + x2^d + x3^d + x4^d = 0 
            then signChar n (a * (x1 + x2 + x3 + x4)) else 0 := by
        congr 1; ext y1; congr 1; ext y2; congr 1; ext y3; congr 1; ext y4
        have ht_inv_ne_zero : t⁻¹ ≠ 0 := by simp [ht]
        have ht_inv_pow_ne_zero : (t⁻¹)^d ≠ 0 := by
          cases d with
          | zero => simp
          | succ n => exact pow_ne_zero _ ht_inv_ne_zero
        simp only [mul_pow]
        rw [← mul_add, ← mul_add, ← mul_add]
        have cond_equiv : (t⁻¹)^d * (y1^d + y2^d + y3^d + y4^d) = 0 ↔ y1^d + y2^d + y3^d + y4^d = 0 := by
          constructor
          · intro h; exact mul_eq_zero.mp h |>.resolve_left ht_inv_pow_ne_zero
          · intro h; simp [h]
        rw [cond_equiv]
        congr 1
        ring_nf
        simp [ht]

/-- `Afun(a,0)` equals the total count `S1count`. -/
lemma Afun_zero (n d : ℕ) (a : GF n) : Afun n d a 0 = S1count n d := by
  unfold Afun S1count
  apply Finset.sum_congr rfl; intro x1 _
  apply Finset.sum_congr rfl; intro x2 _
  apply Finset.sum_congr rfl; intro x3 _
  apply Finset.sum_congr rfl; intro x4 _
  simp

/-- Summing `Afun` over all `t` collapses via orthogonality to `2^n · S0count`. -/
lemma sum_t_Afun (n d : ℕ) (hn : 0 < n) (a : GF n) (ha : a ≠ 0) :
    (∑ t : GF n, Afun n d a t) = 2 ^ n * S0count n d := by
  have key : ∀ x1 x2 x3 x4 : GF n,
      (∑ t : GF n, (if x1 ^ d + x2 ^ d + x3 ^ d + x4 ^ d = 0
          then signChar n (a * t * (x1 + x2 + x3 + x4)) else 0))
      = (if x1 + x2 + x3 + x4 = 0 ∧ x1 ^ d + x2 ^ d + x3 ^ d + x4 ^ d = 0
          then (2 ^ n : ℤ) else 0) := by
    intro x1 x2 x3 x4
    by_cases hd : x1 ^ d + x2 ^ d + x3 ^ d + x4 ^ d = 0
    · have hos : (∑ t : GF n, signChar n (a * t * (x1 + x2 + x3 + x4)))
          = if a * (x1 + x2 + x3 + x4) = 0 then (2 ^ n : ℤ) else 0 := by
        rw [← signChar_orthogonality' n hn (a * (x1 + x2 + x3 + x4))]
        apply Finset.sum_congr rfl; intro t _; congr 1; ring
      simp only [hd, if_true, and_true]
      rw [hos]
      by_cases hsum : x1 + x2 + x3 + x4 = 0
      · simp [hsum]
      · rw [if_neg (mul_ne_zero ha hsum), if_neg hsum]
    · simp only [hd, if_false, and_false, Finset.sum_const_zero]
  unfold Afun S0count
  rw [Finset.mul_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x1 _
  rw [Finset.mul_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x2 _
  rw [Finset.mul_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x3 _
  rw [Finset.mul_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x4 _
  rw [key x1 x2 x3 x4]
  by_cases hc : x1 + x2 + x3 + x4 = 0 ∧ x1 ^ d + x2 ^ d + x3 ^ d + x4 ^ d = 0 <;> simp [hc]

/-- The scaling/character reindexing identity. -/
lemma Sfour_reindex (n d : ℕ) (hn : 0 < n) (a : GF n) (ha : a ≠ 0) :
    (2 ^ n - 1 : ℤ) * Sfour n d a = 2 ^ n * S0count n d - S1count n d := by
  -- ∑_t Afun a t = Afun a 0 + ∑_{t≠0} Afun a t = S1count + (2^n - 1)·Sfour
  have hsplit : (∑ t : GF n, Afun n d a t)
      = Afun n d a 0 + ∑ t ∈ (Finset.univ.erase 0), Afun n d a t := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : GF n))]; ring
  have herase : (∑ t ∈ (Finset.univ.erase (0 : GF n)), Afun n d a t)
      = (2 ^ n - 1 : ℤ) * Sfour n d a := by
    rw [Finset.sum_congr rfl (fun t ht => Afun_eq_Sfour n d a t (Finset.ne_of_mem_erase ht))]
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      card_GF n hn]
    rw [nsmul_eq_mul]; push_cast [Nat.one_le_two_pow]; ring
  rw [sum_t_Afun n d hn a ha, hsplit, Afun_zero] at *
  rw [herase] at hsplit
  linarith [hsplit]

/-- **Total count.**  For a permutation monomial, there are `2^{3n}` quadruples
with `∑ xᵢ^d = 0`. -/
lemma S1count_eq (n d : ℕ) (hn : 0 < n)
    (hbij : Function.Bijective (fun x : GF n => x ^ d)) :
    S1count n d = 2 ^ (3 * n) := by
  unfold S1count
  -- For each (x1, x2, x3), there's exactly one x4 satisfying the equation
  have hinner : ∀ x1 x2 x3 : GF n,
      ∑ x4 : GF n, (if x1 ^ d + x2 ^ d + x3 ^ d + x4 ^ d = 0 then (1 : ℤ) else 0) = 1 := by
    intro x1 x2 x3
    -- Let s = x1^d + x2^d + x3^d, we need x4^d = -s
    set s := x1 ^ d + x2 ^ d + x3 ^ d with hs_def
    -- The condition s + x4^d = 0 is equivalent to x4^d = -s
    have heq : ∀ x4 : GF n, s + x4 ^ d = 0 ↔ x4 ^ d = -s := by
      intro x4
      constructor
      · intro h; linear_combination h
      · intro h; linear_combination h
    simp_rw [heq]
    -- The sum equals the cardinality of {x4 | x4^d = -s}
    have hcard : (∑ x4 : GF n, if x4 ^ d = -s then (1 : ℤ) else 0) =
        (Fintype.card {x : GF n // x ^ d = -s} : ℤ) := by
      rw [Fintype.card_subtype]
      rw [Finset.sum_ite]
      simp only [Finset.sum_const_zero, add_zero]
      rw [Finset.card_eq_sum_ones]
      norm_cast
    rw [hcard]
    -- Since x^d is bijective, there's exactly one preimage
    have hcard1 : Fintype.card {x : GF n // x ^ d = -s} = 1 := by
      -- Use bijectivity: there exists a unique x with x^d = -s
      have hsurj : Function.Surjective (fun x : GF n => x ^ d) := hbij.2
      have hinj : Function.Injective (fun x : GF n => x ^ d) := hbij.1
      -- There exists a unique preimage
      obtain ⟨x₀, hx₀⟩ := hsurj (-s)
      rw [Fintype.card_eq_one_iff]
      use ⟨x₀, hx₀⟩
      intro ⟨x, hx⟩
      congr 1
      exact hinj (hx.trans hx₀.symm)
    simp [hcard1]
  simp_rw [hinner]
  simp [pow_mul]
  have hcard : Fintype.card (GF n) = 2 ^ n := card_GF n hn
  simp [hcard]
  rw [show (8 : ℤ) = 2 ^ 3 by norm_num, ← pow_mul]
  rw [← pow_add, ← pow_add]
  congr 1; omega

/-- The inner pair count `#{(x,z) : D_s(x) = D_s(z)}`, where `D_s(x)=x^d+(x+s)^d`. -/
noncomputable def pairCount (n d : ℕ) (s : GF n) : ℤ :=
  ∑ x1 : GF n, ∑ x3 : GF n,
    (if x1 ^ d + (x1 + s) ^ d + x3 ^ d + (x3 + s) ^ d = 0 then (1 : ℤ) else 0)

/-- Reduce `S0count` to a triple sum: `x4` is forced to be `x1+x2+x3`. -/
lemma S0count_eq_triple (n d : ℕ) :
    S0count n d = ∑ x1 : GF n, ∑ x2 : GF n, ∑ x3 : GF n,
      (if x1 ^ d + x2 ^ d + x3 ^ d + (x1 + x2 + x3) ^ d = 0 then (1 : ℤ) else 0) := by
  unfold S0count
  apply Finset.sum_congr rfl; intro x1 _
  apply Finset.sum_congr rfl; intro x2 _
  apply Finset.sum_congr rfl; intro x3 _
  have h : ∑ x4 : GF n, (if x1 + x2 + x3 + x4 = 0 ∧ x1 ^ d + x2 ^ d + x3 ^ d + x4 ^ d = 0 then (1 : ℤ) else 0) =
           ∑ x4 : GF n, (if x4 = x1 + x2 + x3 ∧ x1 ^ d + x2 ^ d + x3 ^ d + x4 ^ d = 0 then (1 : ℤ) else 0) := by
    apply Finset.sum_congr rfl; intro x4 _
    congr 2
    rw [eq_comm]
    refine propext ⟨fun h => ?_, fun h => ?_⟩
    · rw [h]; exact CharTwo.add_self_eq_zero (x1 + x2 + x3)
    · rw [add_eq_zero_iff_eq_neg] at h
      rw [h]; exact (CharTwo.neg_eq x4).symm
  rw [h]
  by_cases hzero : x1 ^ d + x2 ^ d + x3 ^ d + (x1 + x2 + x3) ^ d = 0
  · have heq : (∑ x4 : GF n, if x4 = x1 + x2 + x3 ∧ x1 ^ d + x2 ^ d + x3 ^ d + x4 ^ d = 0 then (1 : ℤ) else 0) =
               (∑ x4 : GF n, if x4 = x1 + x2 + x3 then (1 : ℤ) else 0) := by
      apply Finset.sum_congr rfl
      intro x4 _
      by_cases hx : x4 = x1 + x2 + x3
      · simp [hx, hzero]
      · simp [hx]
    rw [heq]
    simp [hzero]
  · have heq : (∑ x4 : GF n, if x4 = x1 + x2 + x3 ∧ x1 ^ d + x2 ^ d + x3 ^ d + x4 ^ d = 0 then (1 : ℤ) else 0) = 0 := by
      rw [Finset.sum_eq_zero]
      intro x4 _
      split_ifs with hx
      · exact absurd (by rw [hx.1] at hx; exact hx.2) hzero
      · rfl
    rw [heq]
    simp [hzero]

/-- Reparametrize the triple sum by `s = x1 + x2`. -/
lemma triple_eq_pairCount (n d : ℕ) :
    (∑ x1 : GF n, ∑ x2 : GF n, ∑ x3 : GF n,
      (if x1 ^ d + x2 ^ d + x3 ^ d + (x1 + x2 + x3) ^ d = 0 then (1 : ℤ) else 0))
    = ∑ s : GF n, pairCount n d s := by
  unfold pairCount
  have h1 : (∑ x1 : GF n, ∑ x2 : GF n, ∑ x3 : GF n,
      (if x1 ^ d + x2 ^ d + x3 ^ d + (x1 + x2 + x3) ^ d = 0 then (1 : ℤ) else 0)) =
      ∑ x : GF n × GF n × GF n, (if x.1 ^ d + x.2.1 ^ d + x.2.2 ^ d + (x.1 + x.2.1 + x.2.2) ^ d = 0 then (1 : ℤ) else 0) := by
    conv_lhs => rw [← Finset.sum_product']
    rw [← Finset.sum_product']
    symm
    apply Finset.sum_equiv (Equiv.prodAssoc (GF n) (GF n) (GF n)).symm
    · simp
    · intro i hi
      simp only [Equiv.prodAssoc_symm_apply]
  have h2 : (∑ s : GF n, ∑ x1 : GF n, ∑ x3 : GF n,
      (if x1 ^ d + (x1 + s) ^ d + x3 ^ d + (x3 + s) ^ d = 0 then (1 : ℤ) else 0)) =
      ∑ q : GF n × GF n × GF n, (if q.2.1 ^ d + (q.2.1 + q.1) ^ d + q.2.2 ^ d + (q.2.2 + q.1) ^ d = 0 then (1 : ℤ) else 0) := by
    conv_lhs => rw [← Finset.sum_product']
    rw [← Finset.sum_product']
    symm
    simp_rw [← Finset.univ_product_univ]
    apply Finset.sum_equiv (Equiv.prodAssoc (GF n) (GF n) (GF n)).symm
    · simp
    · intro i hi
      simp only [Equiv.prodAssoc_symm_apply]
  rw [h1, h2]
  symm
  let equiv : (GF n × GF n × GF n) ≃ (GF n × GF n × GF n) :=
    Equiv.ofBijective (fun p => (p.1 + p.2.1, p.1, p.2.2)) ⟨by
      intro a b h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      refine Prod.ext h2 (Prod.ext ?_ h3)
      rw [h2] at h1
      exact add_left_cancel h1, by
      intro p
      refine ⟨(p.2.1, p.1 + p.2.1, p.2.2), ?_⟩
      have h2' : (2 : GF n) = 0 := by rw [show (2 : GF n) = 1 + 1 by norm_cast]; exact CharTwo.add_self_eq_zero _
      have key : (p.2.1 + (p.1 + p.2.1) : GF n) = p.1 := by
        calc p.2.1 + (p.1 + p.2.1) = p.2.1 + p.2.1 + p.1 := by abel
          _ = (2 : GF n) * p.2.1 + p.1 := by rw [show p.2.1 + p.2.1 = 2 * p.2.1 from by ring]
          _ = 0 * p.2.1 + p.1 := by rw [h2']
          _ = 0 + p.1 := by rw [zero_mul]
          _ = p.1 := by ring
      ext <;> simp [key]
  ⟩
  rw [← Finset.sum_equiv equiv]
  · intro i; simp
  · intro i hi
    show (if i.1 ^ d + i.2.1 ^ d + i.2.2 ^ d + (i.1 + i.2.1 + i.2.2) ^ d = 0 then 1 else 0) =
         if ((equiv i).2.1) ^ d + ((equiv i).2.1 + (equiv i).1) ^ d + (equiv i).2.2 ^ d + ((equiv i).2.2 + (equiv i).1) ^ d = 0 then 1 else 0
    simp [equiv]
    have h2' : (2 : GF n) = 0 := by rw [show (2 : GF n) = 1 + 1 by norm_cast]; exact CharTwo.add_self_eq_zero _
    have key1 : (i.1 + (i.1 + i.2.1) : GF n) = i.2.1 := by
      calc i.1 + (i.1 + i.2.1) = i.1 + i.1 + i.2.1 := by abel
        _ = (2 : GF n) * i.1 + i.2.1 := by rw [show i.1 + i.1 = 2 * i.1 from by ring]
        _ = 0 * i.1 + i.2.1 := by rw [h2']
        _ = 0 + i.2.1 := by rw [zero_mul]
        _ = i.2.1 := by ring
    have key2 : (i.2.2 + (i.1 + i.2.1) : GF n) = i.1 + i.2.1 + i.2.2 := by abel
    simp only [key1, key2]

/-- The pair count at `s = 0` is `2^{2n}` (the condition is vacuous). -/
lemma pairCount_zero (n d : ℕ) (hn : 0 < n) : pairCount n d 0 = 2 ^ (2 * n) := by
  unfold pairCount
  simp only [add_zero]
  have h: ∀ x : GF n, x ^ d + x ^ d = 0 := fun x => CharTwo.add_self_eq_zero _
  simp_rw [h]
  simp [h, Finset.card_univ, card_GF n hn]
  rw [← pow_add]
  ring_nf

/-- The pair count at `s ≠ 0` is `2·2^n` (from the APN 2-to-1 property). -/
lemma pairCount_ne (n d : ℕ) (hn : 0 < n) (hAPN : IsAPN (fun x : GF n => x ^ d))
    (s : GF n) (hs : s ≠ 0) : pairCount n d s = 2 * 2 ^ n := by
  have hscale : pairCount n d s = pairCount n d 1 := by
    unfold pairCount
    have hD : ∀ x : GF n, x ^ d + (x + s) ^ d = s ^ d * ((x / s) ^ d + (x / s + 1) ^ d) := by
      intro x
      have h1 : x / s + 1 = (x + s) / s := by rw [div_add_one hs]
      rw [h1]
      have h2 : s ^ d * (((x + s) / s) ^ d) = (x + s) ^ d := by
        rw [mul_comm, ← mul_pow]
        congr 1
        rw [div_mul_cancel₀ _ hs]
      have h3 : s ^ d * ((x / s) ^ d) = x ^ d := by
        rw [mul_comm, ← mul_pow]
        congr 1
        rw [div_mul_cancel₀ _ hs]
      rw [mul_add, h3, h2]
    have heq : ∀ x1 x3 : GF n, x1 ^ d + (x1 + s) ^ d + x3 ^ d + (x3 + s) ^ d = 0
        ↔ (x1 / s) ^ d + ((x1 / s) + 1) ^ d + (x3 / s) ^ d + ((x3 / s) + 1) ^ d = 0 := by
      intro x1 x3
      have h1 := hD x1
      have h2 := hD x3
      have hsd : s ^ d ≠ 0 := pow_ne_zero _ hs
      rw [show x1 ^ d + (x1 + s) ^ d + x3 ^ d + (x3 + s) ^ d =
          (x1 ^ d + (x1 + s) ^ d) + (x3 ^ d + (x3 + s) ^ d) by ring]
      rw [h1, h2]
      rw [show s ^ d * ((x1 / s) ^ d + (x1 / s + 1) ^ d) + s ^ d * ((x3 / s) ^ d + (x3 / s + 1) ^ d) =
          s ^ d * ((x1 / s) ^ d + (x1 / s + 1) ^ d + ((x3 / s) ^ d + (x3 / s + 1) ^ d)) by ring]
      rw [mul_eq_zero]
      simp [hsd]
      ring_nf
    rw [show (∑ x1 : GF n, ∑ x3 : GF n,
        if x1 ^ d + (x1 + s) ^ d + x3 ^ d + (x3 + s) ^ d = 0 then (1 : ℤ) else 0) =
        ∑ x1 : GF n, ∑ x3 : GF n,
        if (x1 / s) ^ d + ((x1 / s) + 1) ^ d + (x3 / s) ^ d + ((x3 / s) + 1) ^ d = 0 then (1 : ℤ) else 0 by
      apply Finset.sum_congr rfl
      intro x1 _
      apply Finset.sum_congr rfl
      intro x3 _
      rw [heq x1 x3]]
    have hkey : ∀ (f : GF n → GF n → ℤ),
        (∑ x1 : GF n, ∑ x3 : GF n, f (x1 / s) (x3 / s)) = ∑ y1 : GF n, ∑ y3 : GF n, f y1 y3 := by
      intro f
      let σ : GF n ≃ GF n := {
        toFun := fun x => x * s
        invFun := fun x => x * s⁻¹
        left_inv := fun x => by simp [hs]
        right_inv := fun x => by simp [hs]
      }
      have h1 : ∀ x, σ x * s⁻¹ = x := fun x => by
        show (x * s) * s⁻¹ = x
        rw [mul_assoc, mul_inv_cancel₀ hs, mul_one]
      calc ∑ x1 : GF n, ∑ x3 : GF n, f (x1 / s) (x3 / s)
          = ∑ y1 : GF n, ∑ x3 : GF n, f ((σ y1) / s) (x3 / s) := by rw [← σ.sum_comp]
        _ = ∑ y1 : GF n, ∑ y3 : GF n, f ((σ y1) / s) ((σ y3) / s) := by
            apply Finset.sum_congr rfl; intro y1 _; rw [← σ.sum_comp]
        _ = ∑ y1 : GF n, ∑ y3 : GF n, f y1 y3 := by simp only [div_eq_mul_inv]; simp [h1]
    specialize hkey (fun y1 y3 => if y1 ^ d + (y1 + 1) ^ d + y3 ^ d + (y3 + 1) ^ d = 0 then (1 : ℤ) else 0)
    rw [hkey]
  rw [hscale]
  have h_atmost : AtMostTwo (fun x : GF n => x ^ d + (x + 1) ^ d) := hAPN 1 (by simp)
  have hD_periodic : ∀ x : GF n, (x + 1) ^ d + ((x + 1) + 1) ^ d = x ^ d + (x + 1) ^ d := by
    intro x
    have : (x + 1) + 1 = x := by
      haveI := Fact.mk (show Nat.Prime 2 by decide)
      simp [add_assoc, CharTwo.add_self_eq_zero]
    rw [this]
    ring
  let D : GF n → GF n := fun x => x ^ d + (x + 1) ^ d
  have hfiber : ∀ x1 : GF n, (Finset.univ.filter (fun x3 => D x3 = D x1)).card = 2 := by
    intro x1
    have hx1_mem : x1 ∈ Finset.univ.filter (fun x3 => D x3 = D x1) := by simp
    have hx1p1_mem : x1 + 1 ∈ Finset.univ.filter (fun x3 => D x3 = D x1) := by
      simp
      exact hD_periodic x1
    have hne : x1 ≠ x1 + 1 := by
      have h1 : (1 : GF n) ≠ 0 := one_ne_zero
      intro heq
      exact h1 (by linear_combination -heq)
    have h_atmost_fiber : ∀ y z w : GF n, D y = D x1 → D z = D x1 → D w = D x1 → y = z ∨ y = w ∨ z = w := by
      intro y z w hy hz hw
      have hyz : D y = D z := by rw [hy, hz]
      have hyw : D y = D w := by rw [hy, hw]
      exact @h_atmost y z w hyz hyw
    have h_Fiber_ge : (Finset.univ.filter (fun x3 => D x3 = D x1)).card ≥ 2 := by
      have : ({x1, x1 + 1} : Finset (GF n)) ⊆ Finset.univ.filter (fun x3 => D x3 = D x1) := by
        intro y hy
        simp at hy ⊢
        rcases hy with rfl | rfl <;> [rfl; exact hD_periodic x1]
      calc (Finset.univ.filter (fun x3 => D x3 = D x1)).card
          ≥ ({x1, x1 + 1} : Finset (GF n)).card := Finset.card_le_card this
        _ = 2 := by simp [hne]
    have h_Fiber_le : (Finset.univ.filter (fun x3 => D x3 = D x1)).card ≤ 2 := by
      by_contra h_gt
      push_neg at h_gt
      obtain ⟨y, z, w, hy, hz, hw, hne_yz, hne_yw, hne_zw⟩ : ∃ y z w : GF n,
          y ∈ Finset.univ.filter (fun x3 => D x3 = D x1) ∧ z ∈ Finset.univ.filter (fun x3 => D x3 = D x1) ∧ w ∈ Finset.univ.filter (fun x3 => D x3 = D x1) ∧
          y ≠ z ∧ y ≠ w ∧ z ≠ w := by
        obtain ⟨S, hS_sub, hS_card⟩ : ∃ S : Finset (GF n), S ⊆ Finset.univ.filter (fun x3 => D x3 = D x1) ∧ S.card = 3 := by
          exact Finset.exists_subset_card_eq (by linarith : 3 ≤ (Finset.univ.filter (fun x3 => D x3 = D x1)).card)
        have := Finset.card_eq_three.mp hS_card
        obtain ⟨y, z, w, hne_yz, hne_yw, hne_zw, hS_eq⟩ := this
        exact ⟨y, z, w, hS_sub (hS_eq.symm ▸ Finset.mem_insert_self _ _),
               hS_sub (hS_eq.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)),
               hS_sub (hS_eq.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))),
               hne_yz, hne_yw, hne_zw⟩
      have := h_atmost_fiber y z w (by simpa using hy) (by simpa using hz) (by simpa using hw)
      rcases this with rfl | rfl | rfl <;> contradiction
    exact le_antisymm h_Fiber_le h_Fiber_ge
  have hsum : pairCount n d 1 = ∑ x1 : GF n, (Finset.univ.filter (fun x3 => D x3 = D x1)).card := by
    unfold pairCount
    simp_rw [D, Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro x1 _
    apply Finset.sum_congr rfl
    intro x3 _
    have hequiv : x1 ^ d + (x1 + 1) ^ d + x3 ^ d + (x3 + 1) ^ d = 0 ↔
                  x3 ^ d + (x3 + 1) ^ d = x1 ^ d + (x1 + 1) ^ d := by
      have hneg : ∀ a : GF n, -a = a := CharTwo.neg_eq
      constructor <;> intro h
      · have h' : x3 ^ d + (x3 + 1) ^ d + (x1 ^ d + (x1 + 1) ^ d) = 0 := by linear_combination h
        rw [eq_neg_of_add_eq_zero_left h', hneg]
      · have : x1 ^ d + (x1 + 1) ^ d + x3 ^ d + (x3 + 1) ^ d =
               x1 ^ d + (x1 + 1) ^ d + (x1 ^ d + (x1 + 1) ^ d) := by linear_combination h
        simp [CharTwo.add_self_eq_zero] at this
        exact this
    simp [hequiv]
  rw [hsum]
  simp_rw [hfiber]
  simp [Finset.sum_const, Finset.card_univ, card_GF n hn]
  ring

/-- **APN count.**  For an APN monomial, the number of quadruples with
`∑ xᵢ = 0` and `∑ xᵢ^d = 0` is `3·2^{2n} - 2·2^n`. -/
lemma S0count_eq (n d : ℕ) (hn : 0 < n)
    (hAPN : IsAPN (fun x : GF n => x ^ d)) :
    S0count n d = 3 * 2 ^ (2 * n) - 2 * 2 ^ n := by
  rw [S0count_eq_triple n d, triple_eq_pairCount n d]
  rw [← Finset.add_sum_erase _ (pairCount n d) (Finset.mem_univ (0 : GF n))]
  rw [pairCount_zero n d hn]
  rw [Finset.sum_congr rfl
    (fun s hs => pairCount_ne n d hn hAPN s (Finset.ne_of_mem_erase hs))]
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    card_GF n hn]
  rw [nsmul_eq_mul]
  have e : (2 : ℤ) ^ (2 * n) = 2 ^ n * 2 ^ n := by rw [← pow_add]; congr 1; omega
  rw [e]; push_cast [Nat.one_le_two_pow]; ring

/-- **Fourth moment identity.**  For a permutation APN monomial and nonzero `a`,
`∑_b W_f(a,b)^4 = 2·2^{3n}`. -/
theorem walsh_fourth_moment_monomial (n d : ℕ) (hn : 0 < n)
    (hbij : Function.Bijective (fun x : GF n => x ^ d))
    (hAPN : IsAPN (fun x : GF n => x ^ d))
    (a : GF n) (ha : a ≠ 0) :
    (∑ b : GF n, (walsh n (fun x => x ^ d) a b) ^ 4) = 2 * 2 ^ (3 * n) := by
  rw [sum_walsh_fourth_eq_Sfour n d hn a]
  -- Determine Sfour from the reindexing identity and the two counts.
  have hre := Sfour_reindex n d hn a ha
  rw [S0count_eq n d hn hAPN, S1count_eq n d hn hbij] at hre
  have hval : Sfour n d a = 2 * 2 ^ (2 * n) := by
    have hne : (2 ^ n - 1 : ℤ) ≠ 0 := by
      have : (2 : ℤ) ≤ 2 ^ n := by
        calc (2 : ℤ) = 2 ^ 1 := by ring
        _ ≤ 2 ^ n := by apply pow_le_pow_right₀ (by norm_num) hn
      linarith
    have harith : (2 ^ n - 1 : ℤ) * Sfour n d a = (2 ^ n - 1 : ℤ) * (2 * 2 ^ (2 * n)) := by
      rw [hre]
      have e1 : (2 : ℤ) ^ (2 * n) = 2 ^ n * 2 ^ n := by rw [← pow_add]; congr 1; omega
      have e2 : (2 : ℤ) ^ (3 * n) = 2 ^ n * 2 ^ n * 2 ^ n := by rw [← pow_add, ← pow_add]; congr 1; omega
      rw [e1, e2]; ring
    exact mul_left_cancel₀ hne harith
  rw [hval]
  have e3 : (2 : ℤ) ^ (3 * n) = 2 ^ n * 2 ^ (2 * n) := by rw [← pow_add]; congr 1; omega
  rw [e3]; ring

end GeneralizedKasami
