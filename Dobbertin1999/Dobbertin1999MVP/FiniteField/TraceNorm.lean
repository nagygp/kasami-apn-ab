import Mathlib
import Dobbertin1999MVP.FiniteField.FrobAlg

/-!
# Foundational Layer F2: Trace and Norm Theory
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

def frobSum (m : ℕ) (x : F) : F :=
  ∑ i ∈ Finset.range m, x ^ (p ^ i)

lemma frobSum_add (m : ℕ) (x y : F) :
    frobSum p m (x + y) = frobSum p m x + frobSum p m y := by
  unfold frobSum
  simp [← Finset.sum_add_distrib, add_pow_char_pow]

lemma frobSum_zero (m : ℕ) : frobSum p m (0 : F) = 0 :=
  Finset.sum_eq_zero fun i _ => zero_pow (pow_ne_zero _ hp.1.ne_zero)

lemma frobSum_neg (m : ℕ) (x : F) : frobSum p m (-x) = -(frobSum p m x) := by
  have h : ∀ i : ℕ, (-x) ^ (p ^ i) = -(x ^ (p ^ i)) := fun i =>
    show (iterateFrobenius F p i) (-x) = -(iterateFrobenius F p i x) from map_neg _ x
  simp [frobSum, h, Finset.sum_neg_distrib]

lemma frobSum_finset_sum {ι : Type*} (s : Finset ι) (f : ι → F) (m : ℕ) :
    frobSum p m (∑ i ∈ s, f i) = ∑ i ∈ s, frobSum p m (f i) := by
  induction s using Finset.induction with
  | empty => simp [frobSum_zero]
  | insert hmem ih => simp_all [frobSum_add]

lemma frobSum_pow_p {n : ℕ} (hn : Fintype.card F = p ^ n) (x : F) :
    (frobSum p n x) ^ p = frobSum p n x := by
  have h_expand : (∑ i ∈ Finset.range n, x ^ (p ^ i)) ^ p = ∑ i ∈ Finset.range n, x ^ (p ^ (i+1)) := by
    induction' n with n ih;
    · simp +decide [ hp.1.ne_zero ];
    · induction' n + 1 with n ih <;> simp_all +decide [ pow_succ, pow_mul, Finset.sum_range_succ ];
      · exact hp.1.ne_zero;
      · rw [ add_pow_char, ih ];
  have h_reindex : ∑ i ∈ Finset.range n, x ^ (p ^ (i + 1)) = ∑ j ∈ Finset.Ico 1 (n + 1), x ^ (p ^ j) := by
    rw [ Finset.sum_Ico_eq_sum_range ] ; ac_rfl;
  simp_all +decide [ Finset.sum_Ico_eq_sub _ ];
  simp_all +decide [ Finset.sum_range_succ, frobSum ];
  rw [ ← hn, FiniteField.pow_card ] ; ring

lemma frobSum_frob_stable {n : ℕ} (hn : Fintype.card F = p ^ n) (x : F) (j : ℕ) :
    (frobSum p n x) ^ (p ^ j) = frobSum p n x := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, pow_mul, ih, frobSum_pow_p p hn]

lemma frobSum_frob_invariant {n : ℕ} (hn : Fintype.card F = p ^ n) (x : F) (j : ℕ) :
    frobSum p n (x ^ (p ^ j)) = frobSum p n x := by
  unfold frobSum
  have h1 : ∀ i, (x ^ (p ^ j)) ^ (p ^ i) = x ^ (p ^ (j + i)) := by
    intro i; rw [← pow_mul, ← pow_add]
  simp_rw [h1]
  have h2 : ∀ i, x ^ (p ^ (j + i)) = (x ^ (p ^ i)) ^ (p ^ j) := by
    intro i; rw [← pow_mul, ← pow_add, add_comm]
  simp_rw [h2, ← finset_sum_frob_eq]
  exact frobSum_frob_stable p hn x j

omit hp [CharP F p] in
lemma frob_prod_factor {n : ℕ} (hn : Fintype.card F = p ^ n) (x y : F)
    (j : ℕ) (hj : j ≤ n) :
    (x * y ^ (p ^ (n - j))) ^ (p ^ j) = x ^ (p ^ j) * y := by
  rw [mul_pow, ← pow_mul, ← pow_add, Nat.sub_add_cancel hj, ← hn, FiniteField.pow_card]

lemma trace_prod_frob {n : ℕ} (hn : Fintype.card F = p ^ n) (x y : F)
    (j : ℕ) (hj : j ≤ n) :
    frobSum p n (x ^ (p ^ j) * y) = frobSum p n (x * y ^ (p ^ (n - j))) := by
  conv_lhs => rw [show x ^ (p ^ j) * y = (x * y ^ (p ^ (n - j))) ^ (p ^ j) from
    (frob_prod_factor p hn x y j hj).symm]
  exact frobSum_frob_invariant p hn _ j

lemma frobSum_ne_zero {n : ℕ} (hn : Fintype.card F = p ^ n) (hn1 : 1 ≤ n) :
    ∃ x : F, frobSum p n x ≠ 0 := by
  contrapose! hn1;
  set P : Polynomial F := Finset.sum (Finset.range n) (fun i => Polynomial.X ^ (p ^ i));
  have hP_zero : P = 0 := by
    refine' Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq _ _ _;
    exact Finset.univ;
    · rcases n with ( _ | n ) <;> simp_all +decide [ Polynomial.degree_lt_iff_coeff_zero ];
      · exact absurd hn ( Nat.ne_of_gt ( Fintype.one_lt_card ) );
      · refine' lt_of_le_of_lt ( Polynomial.degree_sum_le _ _ ) _;
        simp +decide [ Finset.range_add_one ];
        refine' ⟨ mod_cast pow_lt_pow_right₀ hp.1.one_lt n.lt_succ_self, _ ⟩;
        exact lt_of_le_of_lt ( Finset.sup_le fun i hi => WithBot.coe_le_coe.mpr ( pow_le_pow_right₀ hp.1.one_lt.le ( Finset.mem_range_le hi ) ) ) ( WithBot.coe_lt_coe.mpr ( pow_lt_pow_right₀ hp.1.one_lt ( Nat.lt_succ_self _ ) ) );
    · simp +zetaDelta at *;
      simp_all +decide [ Polynomial.eval_finset_sum, frobSum ];
  replace hP_zero := congr_arg ( fun q => Polynomial.coeff q ( p ^ 0 ) ) hP_zero ; simp_all +decide [ Polynomial.coeff_X_pow ];
  rcases n with ( _ | _ | n ) <;> simp_all +decide [ Polynomial.coeff_sum, Polynomial.coeff_X_pow ];
  · simp +zetaDelta at *;
  · rw [ Polynomial.finset_sum_coeff, Finset.sum_eq_single 0 ] at hP_zero <;> simp_all +decide [ Polynomial.coeff_X_pow ];
    exact fun b hb hb' => ne_of_lt ( one_lt_pow₀ hp.1.one_lt hb' )

lemma trace_nondegenerate {n : ℕ} (hn : Fintype.card F = p ^ n) (hn1 : 1 ≤ n)
    {x : F} (hx : x ≠ 0) :
    ∃ y : F, frobSum p n (x * y) ≠ 0 := by
  obtain ⟨z, hz⟩ := frobSum_ne_zero p hn hn1
  exact ⟨z / x, by rwa [mul_div_cancel₀ _ hx]⟩

omit [Fintype F] hp [CharP F p] in
lemma sum_frob_reverse {n m : ℕ} (hm : m ≤ n) (z : F) :
    ∑ i ∈ Finset.range m, z ^ (p ^ (n - i)) =
    ∑ j ∈ Finset.Ico (n - m + 1) (n + 1), z ^ (p ^ j) := by
  apply Finset.sum_bij (fun i hi => n - i);
  · grind +qlia;
  · grind;
  · exact fun b hb => ⟨ n - b, by norm_num at *; omega, by norm_num at *; omega ⟩;
  · exact fun _ _ => rfl

lemma frobSum_adj_expand (m : ℕ) (w z : F) :
    frobSum p n (frobSum p m w * z) =
    ∑ i ∈ Finset.range m, frobSum p n (w ^ (p ^ i) * z) := by
  conv_lhs => rw [show frobSum p m w * z = ∑ i ∈ Finset.range m, w ^ p ^ i * z by
    simp [frobSum, sum_mul]]
  exact frobSum_finset_sum p _ _ n

lemma frobSum_adjoint {n : ℕ} (hn : Fintype.card F = p ^ n) (m : ℕ)
    (hm : m ≤ n) (w z : F) :
    frobSum p n (frobSum p m w * z) =
    frobSum p n (w * ∑ i ∈ Finset.range m, z ^ (p ^ (n - i))) := by
  rw [frobSum_adj_expand]
  conv_rhs => rw [mul_sum, frobSum_finset_sum]
  exact Finset.sum_congr rfl fun i hi =>
    trace_prod_frob p hn w z i (by linarith [Finset.mem_range.mp hi])

lemma frobSum_adjoint_Ico {n : ℕ} (hn : Fintype.card F = p ^ n) (m : ℕ)
    (hm : m ≤ n) (w z : F) :
    frobSum p n (frobSum p m w * z) =
    frobSum p n (w * ∑ j ∈ Finset.Ico (n - m + 1) (n + 1), z ^ (p ^ j)) := by
  rw [frobSum_adjoint p hn m hm w z, sum_frob_reverse p hm z]

end DempwolffMueller
