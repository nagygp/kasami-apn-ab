import Mathlib
import Dobbertin1999MVP.FiniteField.TraceNorm
import Dobbertin1999MVP.FiniteField.ExpArith
import Dobbertin1999MVP.FiniteField.FrobAlg
import Dobbertin1999MVP.FiniteField.AdjointBij

/-!
# Theorem 3.2 — Dempwolff & Müller

L(X)·X^k and L(X)·X^{k'} are permutation polynomials on GF(2ⁿ),
where L(X) = ∑_{i=0}^{m-1} X^{2^i} is the truncated trace,
k = 2^{n-1} - 2^{m-1} - 1, and k·k' ≡ 2^{m-1} (mod 2ⁿ-1).
-/

namespace DempwolffMueller

set_option maxHeartbeats 800000

open Finset BigOperators

-- ═══════════════════════════════════════════
-- Definitions
-- ═══════════════════════════════════════════

/-- The truncated trace map L(x) = ∑_{i=0}^{m-1} x^{2^i}. -/
def truncTrace {F : Type*} [CommSemiring F] (m : ℕ) (x : F) : F :=
  ∑ i ∈ Finset.range m, x ^ (2 ^ i)

/-- The Dickson-like polynomial f_m(x) = ∑_{j=0}^{m-1} x^{2^m + 1 - 2^{j+1}}. -/
noncomputable def dicksonF {F : Type*} [CommSemiring F] (m : ℕ) (x : F) : F :=
  ∑ j ∈ Finset.range m, x ^ (2 ^ m + 1 - 2 ^ (j + 1))

-- ═══════════════════════════════════════════
-- Layer 1 : Additivity
-- ═══════════════════════════════════════════

lemma truncTrace_add {F : Type*} [CommSemiring F] [CharP F 2] (m : ℕ) (x y : F) :
    truncTrace m (x + y) = truncTrace m x + truncTrace m y := by
  simp only [truncTrace, ← Finset.sum_add_distrib]
  congr 1; ext i; exact add_pow_char_pow (p := 2) (n := i) x y

lemma truncTrace_zero {F : Type*} [CommSemiring F] (m : ℕ) :
    truncTrace m (0 : F) = 0 := by simp [truncTrace]

lemma truncTrace_one_eq_one {F : Type*} [CommSemiring F] [CharP F 2]
    (m : ℕ) (hm : Odd m) : truncTrace m (1 : F) = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k + 1 := hm;
  unfold truncTrace;
  simp_all +decide [ show ( 2 : F ) = 0 by exact CharTwo.two_eq_zero ]

/-
═══════════════════════════════════════════
Layer 2 : Telescoping identity
L(x)² + L(x) = x^{2^m} + x
═══════════════════════════════════════════
-/
lemma truncTrace_sq_add_self {F : Type*} [CommSemiring F] [CharP F 2]
    (m : ℕ) (x : F) :
    truncTrace m x ^ 2 + truncTrace m x = x ^ (2 ^ m) + x := by
  unfold truncTrace; induction m <;> simp_all +decide [ Finset.sum_range_succ, pow_succ ] ; ring;
  · rw [ mul_two, CharTwo.add_self_eq_zero ];
  · simp_all +decide [ add_mul, mul_add, pow_mul ] ; ring;
    simp_all +decide [ ← add_assoc, ← two_mul, CharTwo.two_eq_zero ];
    simp_all +decide [ add_comm, add_left_comm, add_assoc, sq ];
    simp_all +decide [ ← add_assoc, ← two_mul, CharTwo.two_eq_zero ]

/-
═══════════════════════════════════════════
Layer 3 : Kernel triviality
═══════════════════════════════════════════

If L(x) = 0 then x^{2^m} = x (from telescoping identity in char 2).
-/
lemma frob_fixed_of_truncTrace_zero {F : Type*} [CommRing F] [CharP F 2]
    (m : ℕ) {x : F} (hLx : truncTrace m x = 0) :
    x ^ (2 ^ m) = x := by
  have h_kernel : truncTrace m x ^ 2 + truncTrace m x = x ^ (2 ^ m) + x :=
    truncTrace_sq_add_self m x
  simp [hLx] at h_kernel
  have h : x ^ 2 ^ m + x = 0 := h_kernel.symm
  have := eq_of_sub_eq_zero (show x ^ 2 ^ m - x = 0 by rw [sub_eq_add_neg, CharTwo.neg_eq]; exact h)
  exact this

/-
If gcd(m,n) = 1 and m odd, then L(x) = 0 implies x = 0 in GF(2^n).
-/
lemma truncTrace_ker_trivial {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (m : ℕ)
    (hm_odd : Odd m) (_hm_pos : 1 < m) (hm_lt : m < n)
    (hcop : Nat.Coprime m n) {x : F} (hLx : truncTrace m x = 0) :
    x = 0 := by
  have h_x_two : x ^ 2 = x := by
    have h_x_gcd : x ^ (2 ^ Nat.gcd m n) = x := by
      have h_exp : x ^ (2 ^ m) = x ∧ x ^ (2 ^ n) = x := by
        exact ⟨ frob_fixed_of_truncTrace_zero m hLx, by rw [ ← hn, FiniteField.pow_card ] ⟩;
      have h_exp : ∀ k l : ℕ, x ^ (2 ^ k) = x → x ^ (2 ^ l) = x → x ^ (2 ^ (Nat.gcd k l)) = x := by
        intros k l hk hl
        have h_exp : ∀ a b : ℕ, x ^ (2 ^ a) = x → x ^ (2 ^ b) = x → x ^ (2 ^ (a % b)) = x := by
          intros a b ha hb
          have h_exp : x ^ (2 ^ (a % b)) = x := by
            have h_exp : x ^ (2 ^ a) = (x ^ (2 ^ (a % b))) ^ (2 ^ (b * (a / b))) := by
              rw [ ← pow_mul, ← pow_add, Nat.mod_add_div ]
            have h_exp : ∀ k : ℕ, (x ^ (2 ^ (a % b))) ^ (2 ^ (b * k)) = x ^ (2 ^ (a % b)) := by
              intro k; induction k <;> simp_all +decide [ pow_succ, pow_mul ] ;
              rw [ pow_right_comm, hb ];
            grind;
          exact h_exp;
        induction' l using Nat.strong_induction_on with l ih generalizing k;
        by_cases hl_zero : l = 0;
        · aesop;
        · rw [ Nat.gcd_comm, Nat.gcd_rec ];
          simpa [ Nat.gcd_comm ] using ih ( k % l ) ( Nat.mod_lt _ ( Nat.pos_of_ne_zero hl_zero ) ) l hl ( h_exp k l hk hl );
      exact h_exp m n ( by tauto ) ( by tauto );
    aesop;
  cases eq_or_ne x 0 <;> simp_all +decide [ sq ];
  exact absurd hLx ( by rw [ truncTrace_one_eq_one m hm_odd ] ; simp +decide )

-- ═══════════════════════════════════════════
-- Layer 4-5 : Dickson polynomial
-- ═══════════════════════════════════════════

/-
x · f_{m+1}(x) = f_m(x)² + x^{2^{m+1}}
-/
lemma dicksonF_recursion_mul {F : Type*} [Field F] [CharP F 2] (m : ℕ) (x : F) :
    x * dicksonF (m + 1) x = dicksonF m x ^ 2 + x ^ (2 ^ (m + 1)) := by
  unfold dicksonF;
  rw [ Finset.mul_sum _ _ _, Finset.sum_range_succ' ];
  simp +decide [ ← pow_succ', ← pow_add, Nat.sub_sub, add_comm 1, add_assoc ];
  rw [ Nat.sub_add_cancel ( Nat.one_le_pow _ _ ( by decide ) ) ];
  rw [ ← Finset.sum_congr rfl fun i hi => ?_ ];
  rotate_left;
  use fun i => x ^ ( 2 * ( 2 ^ m + 1 - 2 ^ ( i + 1 ) ) );
  · rw [ show 2 ^ ( m + 1 ) + 1 - 2 ^ ( i + 2 ) = 2 * ( 2 ^ m + 1 - 2 ^ ( i + 1 ) ) - 1 from ?_ ];
    · rw [ Nat.sub_add_cancel ( Nat.one_le_iff_ne_zero.mpr ( mul_ne_zero two_ne_zero ( Nat.sub_ne_zero_of_lt ( by linarith [ Nat.pow_le_pow_right two_pos ( show i + 1 ≤ m from Finset.mem_range.mp hi ) ] ) ) ) ) ];
    · grind;
  · induction' ( range m ) using Finset.induction <;> simp_all +decide [ pow_succ', pow_mul', Finset.sum_range_succ ];
    grind

/-
f_m(z + z⁻¹) = z^{2^m-1} + z^{-(2^m-1)} for z ≠ 0
-/
lemma dicksonF_functional {F : Type*} [Field F] [CharP F 2]
    (m : ℕ) (hm : 0 < m) {z : F} (hz : z ≠ 0) :
    dicksonF m (z + z⁻¹) = z ^ (2 ^ m - 1) + z⁻¹ ^ (2 ^ m - 1) := by
  induction' m with m ih generalizing z <;> simp_all +decide [ pow_succ' ];
  have h_simp : (z + z⁻¹) * dicksonF (m + 1) (z + z⁻¹) = (z ^ (2 ^ m - 1) + z⁻¹ ^ (2 ^ m - 1)) ^ 2 + (z + z⁻¹) ^ (2 ^ (m + 1)) := by
    by_cases hm : 0 < m <;> simp_all +decide [ dicksonF_recursion_mul ];
    simp +decide [ dicksonF ];
    grind;
  by_cases h : z + z⁻¹ = 0 <;> simp_all +decide [ pow_succ', pow_mul ];
  · have hz_one : z = 1 := by
      have hz_sq : z^2 = 1 := by
        grind
      grind +suggestions;
    simp_all +decide [ CharTwo.add_self_eq_zero ];
    unfold dicksonF; simp +decide [ Finset.sum_range_succ' ] ;
    rw [ Finset.sum_eq_zero ] <;> simp +decide [ Nat.sub_eq_zero_iff_le ];
    exact fun x hx => pow_le_pow_right₀ ( by decide ) ( by linarith );
  · refine' mul_left_cancel₀ h _;
    convert h_simp using 1 ; ring;
    rw [ show 2 ^ m * 2 - 1 = ( 2 ^ m - 1 ) * 2 + 1 by zify ; norm_num ; ring ] ; norm_num [ pow_add, pow_mul, hz ] ; ring;
    simp +decide [ hz, pow_mul', add_pow_char_pow ] ; ring;
    simp +decide [ show 2 ^ m * 2 = ( 2 ^ m - 1 ) * 2 + 2 by zify ; norm_num ; ring, pow_add, pow_mul', hz ] ; ring;
    rw [ show ( 2 : F ) = 0 by exact CharP.cast_eq_zero F 2 ] ; ring;

/-
═══════════════════════════════════════════
Layer 6-8 : Coprimality and power maps
═══════════════════════════════════════════

In char 2: a + a⁻¹ = b + b⁻¹ implies a = b or a = b⁻¹.
-/
lemma eq_or_eq_inv_of_add_inv_eq {F : Type*} [Field F] [CharP F 2]
    {a b : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a + a⁻¹ = b + b⁻¹) : a = b ∨ a = b⁻¹ := by
  grind +splitIndPred

lemma dicksonF_map_ringHom {F K : Type*} [CommSemiring F] [CommSemiring K]
    (f : F →+* K) (m : ℕ) (x : F) :
    dicksonF m (f x) = f (dicksonF m x) := by
  simp [dicksonF, map_sum, map_pow]

/-
═══════════════════════════════════════════
Layer 9 : Dickson injectivity on units
═══════════════════════════════════════════

For x ∈ F* in char 2, ∃ z in AlgClosure with z ≠ 0 and z + z⁻¹ = x.
-/
lemma exists_add_inv_rep {F : Type*} [Field F] [CharP F 2]
    {x : F} (hx : x ≠ 0) :
    ∃ z : AlgebraicClosure F, z ≠ 0 ∧
      z + z⁻¹ = algebraMap F (AlgebraicClosure F) x := by
  obtain ⟨z, hz⟩ : ∃ z : AlgebraicClosure F, z ^ 2 + (algebraMap F (AlgebraicClosure F) x) * z + 1 = 0 := by
    have := @IsAlgClosed.exists_root ( AlgebraicClosure F ) _ _;
    exact this ( Polynomial.X ^ 2 + Polynomial.C ( algebraMap F ( AlgebraicClosure F ) x ) * Polynomial.X + 1 ) ( by erw [ Polynomial.degree_add_eq_left_of_degree_lt ] <;> erw [ Polynomial.degree_add_eq_left_of_degree_lt ] <;> by_cases h : algebraMap F ( AlgebraicClosure F ) x = 0 <;> simp +decide [ h ] ) |> fun ⟨ z, hz ⟩ => ⟨ z, by simpa using hz ⟩;
  refine' ⟨ z, _, _ ⟩; all_goals grind

/-
If z² + az + 1 = 0 and a^{2^n} = a, then z^{2^{2n}} = z.
-/
lemma frob_2n_eq_self_of_quad_root {K : Type*} [Field K] [CharP K 2]
    {n : ℕ} {a z : K} (hz : z ^ 2 + a * z + 1 = 0) (ha : a ^ (2 ^ n) = a) :
    z ^ (2 ^ (2 * n)) = z := by
  have hz_pow : (z ^ (2 ^ n)) ^ 2 + a * (z ^ (2 ^ n)) + 1 = 0 := by
    convert congr_arg ( · ^ 2 ^ n ) hz using 1 <;> ring;
    simp +decide [ add_pow_char_pow, mul_pow, ha ] ; ring;
  have hz_cases : z ^ (2 ^ n) = z ∨ z ^ (2 ^ n) = a + z := by
    grind +ring;
  cases' hz_cases with h h <;> simp_all +decide [ pow_mul', pow_two ];
  rw [ add_pow_char_pow, ha ];
  grind +ring

/-
When m odd and gcd(m,n) = 1, gcd(2^m - 1, 2^{2n} - 1) = 1.
-/
lemma coprime_mersenne_double' {m n : ℕ}
    (hm_odd : Odd m) (hcop : Nat.Coprime m n) :
    Nat.Coprime (2 ^ m - 1) (2 ^ (2 * n) - 1) := by
  have h_coprime : Nat.gcd m (2 * n) = 1 := by
    exact Nat.Coprime.mul_right ( Nat.Coprime.symm ( Nat.prime_two.coprime_iff_not_dvd.mpr <| by simpa [ ← even_iff_two_dvd ] using hm_odd ) ) hcop;
  simp_all +decide [ Nat.Coprime, Nat.Coprime.symm ]

/-
f_m is injective on F* when m odd, gcd(m,n) = 1, |F| = 2^n.
-/
lemma dicksonF_injective_on_units {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (m : ℕ)
    (hm_pos : 0 < m) (hm_odd : Odd m) (hcop : Nat.Coprime m n)
    {x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (hf : dicksonF m x = dicksonF m y) : x = y := by
  have := @exists_add_inv_rep F;
  obtain ⟨z, hz₁, hz₂⟩ := this hx
  obtain ⟨w, hw₁, hw₂⟩ := this hy;
  have h_fun_eq : z ^ (2 ^ m - 1) + z⁻¹ ^ (2 ^ m - 1) = w ^ (2 ^ m - 1) + w⁻¹ ^ (2 ^ m - 1) := by
    have h_fun_eq : dicksonF m (z + z⁻¹) = z ^ (2 ^ m - 1) + z⁻¹ ^ (2 ^ m - 1) ∧ dicksonF m (w + w⁻¹) = w ^ (2 ^ m - 1) + w⁻¹ ^ (2 ^ m - 1) := by
      grind +suggestions;
    have h_fun_eq : dicksonF m (algebraMap F (AlgebraicClosure F) x) = algebraMap F (AlgebraicClosure F) (dicksonF m x) ∧ dicksonF m (algebraMap F (AlgebraicClosure F) y) = algebraMap F (AlgebraicClosure F) (dicksonF m y) := by
      exact ⟨ dicksonF_map_ringHom _ _ _, dicksonF_map_ringHom _ _ _ ⟩;
    aesop;
  have h_eq_or_inv : z ^ (2 ^ m - 1) = w ^ (2 ^ m - 1) ∨ z ^ (2 ^ m - 1) = w⁻¹ ^ (2 ^ m - 1) := by
    have := @eq_or_eq_inv_of_add_inv_eq ( AlgebraicClosure F );
    convert this ( pow_ne_zero ( 2 ^ m - 1 ) hz₁ ) ( pow_ne_zero ( 2 ^ m - 1 ) hw₁ ) _ using 1;
    · rw [ inv_pow ];
    · simpa using h_fun_eq
  have h_eq_or_inv' : z = w ∨ z = w⁻¹ := by
    have h_eq_or_inv' : z ^ (2 ^ (2 * n) - 1) = 1 ∧ w ^ (2 ^ (2 * n) - 1) = 1 := by
      have h_eq_or_inv' : z ^ (2 ^ (2 * n)) = z ∧ w ^ (2 ^ (2 * n)) = w := by
        have h_eq_or_inv' : ∀ (z : AlgebraicClosure F), z ^ 2 + (algebraMap F (AlgebraicClosure F)) x * z + 1 = 0 → z ^ (2 ^ (2 * n)) = z := by
          intros z hz
          have h_eq_or_inv' : (algebraMap F (AlgebraicClosure F)) x ^ (2 ^ n) = (algebraMap F (AlgebraicClosure F)) x := by
            rw [ ← hn, ← map_pow, FiniteField.pow_card ];
          apply frob_2n_eq_self_of_quad_root; assumption; assumption;
        have h_eq_or_inv' : ∀ (z : AlgebraicClosure F), z ^ 2 + (algebraMap F (AlgebraicClosure F)) y * z + 1 = 0 → z ^ (2 ^ (2 * n)) = z := by
          intros z hz
          apply frob_2n_eq_self_of_quad_root;
          exact hz;
          rw [ ← hn, ← map_pow, FiniteField.pow_card ];
        grind +ring;
      exact ⟨ mul_left_cancel₀ hz₁ <| by rw [ ← pow_succ', Nat.sub_add_cancel ( Nat.one_le_pow _ _ ( by decide ) ) ] ; aesop, mul_left_cancel₀ hw₁ <| by rw [ ← pow_succ', Nat.sub_add_cancel ( Nat.one_le_pow _ _ ( by decide ) ) ] ; aesop ⟩;
    have h_coprime : Nat.Coprime (2 ^ m - 1) (2 ^ (2 * n) - 1) :=
      coprime_mersenne_double' hm_odd hcop
    have h_eq_or_inv' : ∀ {a b : AlgebraicClosure F}, a ^ (2 ^ m - 1) = b ^ (2 ^ m - 1) → a ^ (2 ^ (2 * n) - 1) = 1 → b ^ (2 ^ (2 * n) - 1) = 1 → a = b := by
      intros a b hab ha hb
      have h_eq_or_inv' : (a / b) ^ (2 ^ m - 1) = 1 ∧ (a / b) ^ (2 ^ (2 * n) - 1) = 1 := by
        by_cases hb : b = 0 <;> simp_all +decide [ div_pow ];
        rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.pow_succ' ];
        · exact absurd hn ( Nat.ne_of_gt ( Fintype.one_lt_card ) );
        · exact absurd hb ( by rw [ zero_pow ( Nat.sub_ne_zero_of_lt ( by linarith [ Nat.pow_le_pow_right two_pos ( show 2 * ( n + 1 + 1 ) ≥ 2 by linarith ) ] ) ) ] ; norm_num );
      have h_eq_or_inv' : (a / b) ^ Nat.gcd (2 ^ m - 1) (2 ^ (2 * n) - 1) = 1 := by
        rw [ Nat.gcd_comm, pow_gcd_eq_one ] ; aesop;
      simp_all +decide [ Nat.Coprime, Nat.Coprime.gcd_eq_one ];
      exact eq_of_div_eq_one h_eq_or_inv';
    cases' h_eq_or_inv with h h;
    · exact Or.inl ( h_eq_or_inv' h ( by tauto ) ( by tauto ) );
    · specialize @h_eq_or_inv' z w⁻¹ ; aesop;
  cases' h_eq_or_inv' with h h <;> simp_all +decide [ add_comm ]

/-
═══════════════════════════════════════════
Layer 10 : Reduction to Dickson
═══════════════════════════════════════════

L(x⁻¹)² · x^{2^m+1} = f_m(x) for x ≠ 0
-/
lemma truncTrace_sq_mul_inv_eq_dicksonF {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (m : ℕ) {x : F} (hx : x ≠ 0) :
    truncTrace m x⁻¹ ^ 2 * x ^ (2 ^ m + 1) = dicksonF m x := by
  have h_expand : (truncTrace m x⁻¹) ^ 2 = ∑ i ∈ Finset.range m, x⁻¹ ^ (2 ^ (i + 1)) := by
    show truncTrace m x⁻¹ ^ (2 ^ 1) = _
    rw [truncTrace, truncTrace_frob_output_general 2 m x⁻¹ 1]
  rw [ h_expand, Finset.sum_mul ];
  refine' Finset.sum_congr rfl fun i hi => _;
  rw [ inv_pow, inv_mul_eq_div, div_eq_iff ( pow_ne_zero _ hx ) ];
  rw [ ← pow_add, Nat.sub_add_cancel ( show 2 ^ ( i + 1 ) ≤ 2 ^ m + 1 from Nat.le_succ_of_le ( pow_le_pow_right₀ ( by decide ) ( by linarith [ Finset.mem_range.mp hi ] ) ) ) ]

/-
═══════════════════════════════════════════
Layer 11 : Main injectivity of L(x)·x^k
═══════════════════════════════════════════

L(x)·x^k is injective on F*.
-/
lemma LxXk_injective_on_units {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (m : ℕ)
    (hm_pos : 1 < m) (hm_odd : Odd m) (hm_lt : m < n)
    (hcop : Nat.Coprime m n)
    {x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (heq : truncTrace m x * x ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1) =
           truncTrace m y * y ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) :
    x = y := by
  have h_exp : x ^ (2 * (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) * x ^ (2 ^ m + 1) = 1 ∧ y ^ (2 * (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) * y ^ (2 ^ m + 1) = 1 := by
    have h_exp : 2 * (2 ^ (n - 1) - 2 ^ (m - 1) - 1) + (2 ^ m + 1) = 2 ^ n - 1 := by
      rcases n with ( _ | _ | n ) <;> rcases m with ( _ | _ | m ) <;> simp_all +decide [ pow_succ' ];
      exact eq_tsub_of_add_eq ( by linarith [ Nat.sub_add_cancel ( show 2 * 2 ^ n ≥ 2 * 2 ^ m from Nat.mul_le_mul_left 2 ( pow_le_pow_right₀ ( by decide ) hm_lt.le ) ), Nat.sub_add_cancel ( show 2 * 2 ^ n - 2 * 2 ^ m ≥ 1 from Nat.sub_pos_of_lt ( by gcongr ; linarith ) ) ] );
    simp +decide [ ← pow_add, h_exp ];
    exact ⟨ by rw [ ← hn, FiniteField.pow_card_sub_one_eq_one x hx ], by rw [ ← hn, FiniteField.pow_card_sub_one_eq_one y hy ] ⟩;
  have h_sq : (truncTrace m x) ^ 2 * x ^ (-(2 ^ m + 1) :) = (truncTrace m y) ^ 2 * y ^ (-(2 ^ m + 1) :) := by
    have h_sq : (truncTrace m x * x ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) ^ 2 = (truncTrace m y * y ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) ^ 2 := by
      rw [heq];
    convert h_sq using 1 <;> norm_cast <;> simp_all +decide [ mul_pow, pow_mul' ];
    · grind;
    · exact Or.inl ( inv_eq_of_mul_eq_one_left h_exp.2 );
  have h_dickson : dicksonF m x⁻¹ = dicksonF m y⁻¹ := by
    convert h_sq using 1;
    · convert truncTrace_sq_mul_inv_eq_dicksonF m ( inv_ne_zero hx ) |> Eq.symm using 1 ; simp +decide [ hx, hy, pow_add, pow_mul ] ; ring;
      group;
      rw [ ← zpow_add₀ hx ] ; ring ; norm_num;
    · convert truncTrace_sq_mul_inv_eq_dicksonF m ( inv_ne_zero hy ) using 1 ; simp +decide [ zpow_neg, zpow_ofNat ];
      · convert truncTrace_sq_mul_inv_eq_dicksonF m ( inv_ne_zero hy ) |> Eq.symm using 1 ; simp +decide [ zpow_neg, zpow_ofNat ];
      · convert truncTrace_sq_mul_inv_eq_dicksonF m ( inv_ne_zero hy ) using 1 ; simp +decide [ zpow_neg, zpow_ofNat ];
        rw [ ← zpow_natCast, ← zpow_neg ] ; group ; norm_num;
  have := dicksonF_injective_on_units hn m ( by linarith ) hm_odd hcop ( inv_ne_zero hx ) ( inv_ne_zero hy ) h_dickson; aesop;

/-
L(x)·x^k is a bijection on F.
-/
lemma LxXk_bijective {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (m : ℕ)
    (hm_pos : 1 < m) (hm_odd : Odd m) (hm_lt : m < n)
    (hcop : Nat.Coprime m n) :
    Function.Bijective (fun x : F =>
      truncTrace m x * x ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) := by
  refine' And.intro _ ( Finite.injective_iff_surjective.mp _ );
  · intro x y hxy
    by_cases hx : x = 0;
    · by_cases hy : y = 0 <;> simp_all +decide [ truncTrace_zero ];
      exact Eq.symm ( truncTrace_ker_trivial hn m hm_odd hm_pos hm_lt hcop hxy );
    · by_cases hy : y = 0 <;> simp_all +decide;
      · simp_all +decide [ truncTrace_zero ];
        exact absurd ( truncTrace_ker_trivial hn m hm_odd hm_pos hm_lt hcop hxy ) hx;
      · apply LxXk_injective_on_units hn m hm_pos hm_odd hm_lt hcop hx hy hxy;
  · intro x y hxy
    by_cases hx : x = 0
    ·
      by_cases hy : y = 0 <;> simp_all +decide [ truncTrace_zero ];
      exact Eq.symm ( truncTrace_ker_trivial hn m hm_odd hm_pos hm_lt hcop hxy )
    by_cases hy : y = 0
    ·
      simp_all +decide [ truncTrace_zero ];
      exact absurd ( truncTrace_ker_trivial hn m hm_odd hm_pos hm_lt hcop hxy ) hx
    have h_eq : x = y := by
      exact LxXk_injective_on_units hn m hm_pos hm_odd hm_lt hcop hx hy hxy
    exact h_eq

/-
═══════════════════════════════════════════
Layer 12 : The k' part
═══════════════════════════════════════════

Frobenius adjoint relation for the truncated trace.
-/
lemma truncTrace_adj_frob {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (m : ℕ) (hm : m ≤ n) (x : F) :
    (∑ i ∈ Finset.Ico (n - m + 1) (n + 1), x ^ (2 ^ i)) ^ (2 ^ (m - 1)) =
    truncTrace m x := by
  by_cases hm : m = 0;
  · aesop;
  · have h_frob : (∑ i ∈ Finset.Ico (n - m + 1) (n + 1), x ^ (2 ^ i)) ^ (2 ^ (m - 1)) = ∑ i ∈ Finset.Ico (n - m + 1) (n + 1), x ^ (2 ^ (i + (m - 1))) := by
      induction' ( Finset.Ico ( n - m + 1 ) ( n + 1 ) ) using Finset.induction <;> simp_all +decide [ pow_add, pow_mul ];
      rw [ add_pow_char_pow, ‹ ( ∑ i ∈ _, x ^ 2 ^ i ) ^ 2 ^ ( m - 1 ) = _ › ];
    have h_sum : ∑ i ∈ Finset.Ico (n - m + 1) (n + 1), x ^ (2 ^ (i + (m - 1))) = ∑ i ∈ Finset.range m, x ^ (2 ^ ((n - m + 1 + i + (m - 1)) % n)) := by
      have h_sum : ∀ i ∈ Finset.Ico (n - m + 1) (n + 1), x ^ (2 ^ (i + (m - 1))) = x ^ (2 ^ ((i + (m - 1)) % n)) := by
        intro i hi;
        exact frob_mod 2 hn x (i + (m - 1))
      rw [ Finset.sum_congr rfl h_sum, Finset.sum_Ico_eq_sum_range ];
      rw [ show n + 1 - ( n - m + 1 ) = m by omega ];
    have h_exp : ∀ i ∈ Finset.range m, (n - m + 1 + i + (m - 1)) % n = i := by
      intro i hi; rw [ Nat.mod_eq_sub_mod ] ;
      · rw [ Nat.mod_eq_of_lt ] <;> norm_num at * <;> omega;
      · linarith [ Nat.sub_add_cancel ‹m ≤ n›, Nat.sub_add_cancel ( Nat.one_le_iff_ne_zero.mpr hm ), Finset.mem_range.mp hi ];
    rw [ h_frob, h_sum, Finset.sum_congr rfl fun i hi => by rw [ h_exp i hi ] ] ; rfl

/-
L(x)·x^{k'} is a permutation polynomial.
-/
lemma LxXk'_bijective {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (m : ℕ)
    (hm_pos : 1 < m) (hm_odd : Odd m) (hm_lt : m < n)
    (hcop : Nat.Coprime m n) (k' : ℕ)
    (hk' : (2 ^ (n - 1) - 2 ^ (m - 1) - 1) * k' % (2 ^ n - 1) =
            2 ^ (m - 1) % (2 ^ n - 1)) :
    Function.Bijective (fun x : F => truncTrace m x * x ^ k') := by
  apply adjoint_swap_bij;
  exact hn;
  grind +suggestions;
  rotate_left;
  exact fun a b => truncTrace_add m a b;
  case L₁ => exact fun x => ∑ i ∈ Finset.Ico ( n - m + 1 ) ( n + 1 ), x ^ ( 2 ^ i );
  case e => exact ( 2 ^ ( n - 1 ) - 2 ^ ( m - 1 ) - 1 ) * 2 ^ ( n - m + 1 );
  · intro w z; exact (by
    convert frobSum_adjoint_Ico _ _ _ _ _ using 1;
    rotate_left;
    exact F;
    all_goals try infer_instance;
    exact ⟨ Nat.prime_two ⟩;
    exact n;
    exact hn;
    exact m;
    exact le_of_lt hm_lt;
    bv_omega;
    constructor <;> intro h;
    · convert frobSum_adjoint_Ico _ _ _ _ _ using 1;
      all_goals try infer_instance;
      · exact hn;
      · grobner;
    · convert h w |> Eq.symm using 1;
      · rw [ mul_comm ];
      · simp +decide [ mul_comm, frobSum, truncTrace ]);
  · apply trace_nondegenerate;
    · exact hn;
    · grind;
  · rw [ hn ];
    rw [ mul_right_comm, Nat.ModEq.mul_right _ hk' ];
    rw [ ← pow_add, show m - 1 + ( n - m + 1 ) = n by omega ];
    exact Nat.ModEq.symm ( Nat.modEq_of_dvd <| by simpa );
  · have h_bijective : Function.Bijective (fun x : F => truncTrace m x * x ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) := by
      apply LxXk_bijective hn m hm_pos hm_odd hm_lt hcop;
    have h_bijective : Function.Bijective (fun x : F => (truncTrace m x * x ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) ^ (2 ^ (n - m + 1))) := by
      convert frob_comp_bijective_right ( p := 2 ) h_bijective ( n - m + 1 ) using 1;
    convert h_bijective using 2;
    rw [ mul_pow, ← pow_mul, ← truncTrace_adj_frob hn m ( by linarith ) ];
    rw [ ← pow_mul, ← pow_add, add_comm ];
    have h_frob : ∀ x : F, x ^ (2 ^ n) = x := by
      exact fun x => by rw [ ← hn, FiniteField.pow_card ] ;
    grind +locals;
  · simp +decide [ ← Finset.sum_add_distrib, add_pow_char_pow ]

-- ═══════════════════════════════════════════
-- Main theorem
-- ═══════════════════════════════════════════

/-- **Theorem 3.2** (Dempwolff–Müller). L(X)·X^k is a permutation polynomial on GF(2ⁿ). -/
theorem theorem_3_2 {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (m : ℕ)
    (hm_pos : 1 < m) (hm_odd : Odd m) (hm_lt : m < n)
    (hcop : Nat.Coprime m n) :
    Function.Bijective (fun x : F =>
      truncTrace m x * x ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) :=
  LxXk_bijective hn m hm_pos hm_odd hm_lt hcop

end DempwolffMueller
