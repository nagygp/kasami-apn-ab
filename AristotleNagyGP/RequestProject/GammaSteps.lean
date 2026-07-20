import RequestProject.basic

open scoped BigOperators

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace GeneralizedKasami

/-- The coefficient `c = γ^(2^k+1) + γ`. -/
noncomputable def gammaCoefficient (n k : ℕ) (gamma : GF n) : GF n :=
  gamma ^ (2 ^ k + 1) + gamma

/-- The polynomial `Q(X) = c X^(2^k) + γ^2 X + γ`. -/
noncomputable def gammaPolynomial (n k : ℕ) (gamma : GF n) : Polynomial (GF n) :=
  Polynomial.C (gammaCoefficient n k gamma) * Polynomial.X ^ (2 ^ k) +
    Polynomial.C (gamma ^ 2) * Polynomial.X + Polynomial.C gamma

@[simp] lemma gammaPolynomial_eval (n k : ℕ) (gamma z : GF n) :
    (gammaPolynomial n k gamma).eval z =
      gammaCoefficient n k gamma * z ^ (2 ^ k) + gamma ^ 2 * z + gamma := by
  unfold gammaPolynomial; simp +decide [ Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C ] ;

/-- Root equation for `gammaPolynomial`, under the nonzero coefficient parameter. -/
lemma gammaPolynomial_eq_zero_iff (n k : ℕ) (gamma z : GF n)
    (hgamma : gamma ≠ 0) :
    (gammaPolynomial n k gamma).eval z = 0 ↔
      z ^ (2 ^ k) = gamma * z + (gamma * z) ^ (2 ^ k) + 1 := by
  rw [ show gammaPolynomial n k gamma = Polynomial.C ( gamma ^ ( 2 ^ k + 1 ) + gamma ) * Polynomial.X ^ ( 2 ^ k ) + Polynomial.C ( gamma ^ 2 ) * Polynomial.X + Polynomial.C gamma from rfl ] ; simp +decide [ Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C ] ; ring;
  grind +ring

/-- Iterated Frobenius form of the root equation. -/
lemma gammaPolynomial_eq_zero_iff_iterate (n k i : ℕ) (gamma z : GF n)
    (hgamma : gamma ≠ 0) :
    (gammaPolynomial n k gamma).eval z = 0 ↔
      z ^ (2 ^ ((i + 1) * k)) =
        (gamma * z) ^ (2 ^ (i * k)) +
        (gamma * z) ^ (2 ^ ((i + 1) * k)) + 1 := by
  convert gammaPolynomial_eq_zero_iff n k gamma z hgamma using 1;
  -- Since Frobenius is injective in characteristic two, we can apply it to both sides of the equation.
  have h_frobenius : Function.Injective (fun x : GF n => x ^ (2 ^ (i * k))) := by
    intro x y hxy;
    have h_frobenius : ∀ x y : GF n, x ^ (2 ^ (i * k)) = y ^ (2 ^ (i * k)) → x = y := by
      intro x y hxy
      have h_frobenius : (x - y) ^ (2 ^ (i * k)) = 0 := by
        convert sub_eq_zero.mpr hxy using 1;
        haveI := Fact.mk ( show Nat.Prime 2 by decide ) ; simp +decide [ sub_pow_char_pow ] ;
      exact sub_eq_zero.mp ( eq_zero_of_pow_eq_zero h_frobenius );
    exact h_frobenius x y hxy;
  convert h_frobenius.eq_iff using 1 ; ring;
  rw [ add_pow_char_pow, add_pow_char_pow ] ; ring

/-- The trace of a root is the trace of `1`, namely `n mod 2`. -/
lemma trace_sum_of_gammaPolynomial_root
    (n k : ℕ) (gamma z : GF n) (hn : 0 < n) (hgamma : gamma ≠ 0)
    (hz : (gammaPolynomial n k gamma).eval z = 0) :
    ∑ j ∈ Finset.range n, z ^ (2 ^ j) =
      algebraMap (ZMod 2) (GF n) (n : ZMod 2) := by
  -- From gammaPolynomial_eq_zero_iff obtain z^(2^k)=gamma*z+(gamma*z)^(2^k)+1.
  have hz_pow : z ^ (2 ^ k) = gamma * z + (gamma * z) ^ (2 ^ k) + 1 := by
    grind +suggestions;
  -- Apply the absolute trace sum to both sides of the equation $z^{2^k} = \gamma z + (\gamma z)^{2^k} + 1$.
  have h_trace : (∑ j ∈ Finset.range n, (z ^ (2 ^ k)) ^ (2 ^ j)) = (∑ j ∈ Finset.range n, (gamma * z) ^ (2 ^ j)) + (∑ j ∈ Finset.range n, ((gamma * z) ^ (2 ^ k)) ^ (2 ^ j)) + (∑ j ∈ Finset.range n, 1 ^ (2 ^ j)) := by
    simp +decide only [hz_pow, add_pow_char_pow, ← Finset.sum_add_distrib];
  -- Use trace_sum_frobenius for z and gamma*z to show trace(z^(2^k))=trace(z), and the trace of 1 is the image of n mod 2.
  have h_trace_simplified : (∑ j ∈ Finset.range n, z ^ (2 ^ (k + j))) = (∑ j ∈ Finset.range n, z ^ (2 ^ j)) ∧ (∑ j ∈ Finset.range n, (gamma * z) ^ (2 ^ (k + j))) = (∑ j ∈ Finset.range n, (gamma * z) ^ (2 ^ j)) := by
    have h_trace_simplified : ∀ x : GF n, (∑ j ∈ Finset.range n, x ^ (2 ^ (k + j))) = (∑ j ∈ Finset.range n, x ^ (2 ^ j)) := by
      intro x
      have := trace_sum_frobenius n k x hn
      simp_all +decide [ pow_add, pow_mul ];
      convert this using 1 ; ring;
      induction' ( Finset.range n ) using Finset.induction <;> simp_all +decide [ pow_mul' ];
      rw [ add_pow_char_pow ];
    exact ⟨ h_trace_simplified z, h_trace_simplified ( gamma * z ) ⟩;
  simp_all +decide [ pow_add, pow_mul ];
  grobner

lemma trace_sum_of_gammaPolynomial_root_of_even
    (n k : ℕ) (gamma z : GF n) (hn : 0 < n) (hgamma : gamma ≠ 0)
    (hneven : Even n) (hz : (gammaPolynomial n k gamma).eval z = 0) :
    ∑ j ∈ Finset.range n, z ^ (2 ^ j) = 0 := by
  convert trace_sum_of_gammaPolynomial_root n k gamma z hn hgamma hz using 1;
  obtain ⟨ m, rfl ⟩ := even_iff_two_dvd.mp hneven;
  simp +decide

/-- The sum occurring in the generalized Kasami polynomial, written with a
range so that its terms have indices `1, ..., kInv`. -/
noncomputable def iteratedKasamiSum (n k kInv : ℕ) (z : GF n) : GF n :=
  ∑ i ∈ Finset.range kInv, z ^ (2 ^ ((i + 1) * k))

/-- The iterated sum telescopes, with constant term `kInv mod 2`. -/
lemma iteratedKasamiSum_of_gammaPolynomial_root
    (n k kInv : ℕ) (gamma z : GF n)
    (hn : 0 < n) (hgamma : gamma ≠ 0)
    (hInv : k * kInv ≡ 1 [MOD n])
    (hz : (gammaPolynomial n k gamma).eval z = 0) :
    iteratedKasamiSum n k kInv z =
      gamma * z + (gamma * z) ^ 2 +
        algebraMap (ZMod 2) (GF n) (kInv : ZMod 2) := by
  -- By changing the summation index, we can rewrite the sum as a telescoping series.
  have h_telescope : ∑ i ∈ Finset.range kInv, z ^ (2 ^ ((i + 1) * k)) = ∑ i ∈ Finset.range kInv, ((gamma * z) ^ (2 ^ (i * k)) + (gamma * z) ^ (2 ^ ((i + 1) * k)) + 1) := by
    exact Finset.sum_congr rfl fun i hi => gammaPolynomial_eq_zero_iff_iterate n k i gamma z hgamma |>.1 hz;
  -- The series $\sum_{i=0}^{kInv-1} (u_i + u_{i+1} + 1)$ telescopes to $u_0 + u_{kInv} + kInv$.
  have h_telescope_sum : ∑ i ∈ Finset.range kInv, ((gamma * z) ^ (2 ^ (i * k)) + (gamma * z) ^ (2 ^ ((i + 1) * k)) + 1) = (gamma * z) ^ (2 ^ (0 * k)) + (gamma * z) ^ (2 ^ (kInv * k)) + kInv := by
    have h_telescope_sum : ∀ m : ℕ, ∑ i ∈ Finset.range m, ((gamma * z) ^ (2 ^ (i * k)) + (gamma * z) ^ (2 ^ ((i + 1) * k)) + 1) = (gamma * z) ^ (2 ^ (0 * k)) + (gamma * z) ^ (2 ^ (m * k)) + m := by
      intro m; induction m <;> simp_all +decide [ Finset.sum_range_succ ] ; ring;
      · grind;
      · grind;
    apply h_telescope_sum;
  -- By `gf_frobenius_mod`, since `kInv * k ≡ 1 [MOD n]`, we have `(gamma * z) ^ (2 ^ (kInv * k)) = (gamma * z) ^ 2`.
  have h_frobenius : (gamma * z) ^ (2 ^ (kInv * k)) = (gamma * z) ^ (2 ^ 1) := by
    convert gf_frobenius_mod n ( kInv * k ) 1 ( gamma * z ) hn ( by simpa [ mul_comm ] using hInv ) using 1;
  unfold iteratedKasamiSum; aesop;

/-- When `kInv` is even, the constant term in the telescoping identity vanishes. -/
lemma iteratedKasamiSum_of_gammaPolynomial_root_of_even
    (n k kInv : ℕ) (gamma z : GF n)
    (hn : 0 < n) (hgamma : gamma ≠ 0) (hkInvEven : Even kInv)
    (hInv : k * kInv ≡ 1 [MOD n])
    (hz : (gammaPolynomial n k gamma).eval z = 0) :
    iteratedKasamiSum n k kInv z = gamma * z + (gamma * z) ^ 2 := by
  obtain ⟨ m, rfl ⟩ := even_iff_two_dvd.mp hkInvEven; simp +decide [ iteratedKasamiSum_of_gammaPolynomial_root n k ( 2 * m ) gamma z hn hgamma hInv hz ] ;

/-- The final identity, with the parity congruence represented as equality in the
prime subfield of `GF(2^n)`. -/
lemma gammaPolynomial_root_final_identity
    (n k kInv : ℕ) (a : Fin 2) (gamma z : GF n)
    (hn : 0 < n) (hgamma : gamma ≠ 0)
    (hInv : k * kInv ≡ 1 [MOD n])
    (hz : (gammaPolynomial n k gamma).eval z = 0) :
    gammaCoefficient n k gamma * z ^ (2 ^ k + 1) +
        iteratedKasamiSum n k kInv z +
        algebraMap (ZMod 2) (GF n) a *
          (∑ j ∈ Finset.range n, z ^ (2 ^ j)) =
      algebraMap (ZMod 2) (GF n)
        ((kInv + a.val * n : ℕ) : ZMod 2) := by
  rw [ iteratedKasamiSum_of_gammaPolynomial_root n k kInv gamma z hn hgamma hInv hz ];
  rw [ trace_sum_of_gammaPolynomial_root n k gamma z hn hgamma hz ] ; ring!;
  fin_cases a <;> simp +decide [ gammaPolynomial ] at *; all_goals convert congr_arg ( · * z ) hz using 1 <;> ring

end GeneralizedKasami