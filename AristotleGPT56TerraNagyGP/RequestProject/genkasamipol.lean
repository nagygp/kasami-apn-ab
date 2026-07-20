import RequestProject.PairSteps
import RequestProject.EllSteps

open scoped BigOperators

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace GeneralizedKasami

/-
A solution of the Kasami equation makes its corresponding `eTerm`
vanish (addition and subtraction coincide in characteristic two).
-/
lemma eTerm_eq_zero_of_kasamiEquation
    (n k kInv : ℕ) (a : Fin 2) (gamma x : GF n)
    (hx : gammaCoefficient n k gamma * x ^ (2 ^ k + 1) =
      equationRHS n k kInv a x) :
    eTerm n k kInv a gamma x = 0 := by
  convert sub_eq_zero.mpr hx using 1;
  unfold eTerm equationRHS iteratedKasamiSum;
  erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ];
  grind

/-
The odd-parity assumption says that its image in `GF(2^n)` is one.
-/
lemma parity_algebraMap_eq_one
    (n kInv : ℕ) (a : Fin 2)
    (hparity : kInv + a.val * n ≡ 1 [MOD 2]) :
    algebraMap (ZMod 2) (GF n)
      ((kInv + a.val * n : ℕ) : ZMod 2) = 1 := by
  rw [ ← ZMod.natCast_eq_natCast_iff ] at * ; aesop;

/-
Under odd parity, a solution of the Kasami equation cannot lie in the
zero fiber of `Q`.
-/
lemma kasamiEquation_not_gammaPolynomial_zero
    (n k kInv : ℕ) (a : Fin 2) (gamma x : GF n)
    (hn : 0 < n) (hgamma : gamma ≠ 0)
    (hInv : k * kInv ≡ 1 [MOD n])
    (hparity : kInv + a.val * n ≡ 1 [MOD 2])
    (hx : gammaCoefficient n k gamma * x ^ (2 ^ k + 1) =
      equationRHS n k kInv a x)
    (hQ : (gammaPolynomial n k gamma).eval x = 0) : False := by
  have := GeneralizedKasami.gammaPolynomial_root_final_identity n k kInv a gamma x hn hgamma hInv hQ;
  have := @GeneralizedKasami.eTerm_eq_zero_of_kasamiEquation n k kInv a gamma x hx; simp_all +decide [ GeneralizedKasami.eTerm ] ;
  have := @GeneralizedKasami.parity_algebraMap_eq_one n kInv a hparity; simp_all +decide [ Nat.ModEq ] ;

/-
Dobbertin's second case: when `c = γ^(2^k+1)+γ`, odd parity still
forces uniqueness among nonzero solutions of the original Kasami equation.
-/
lemma kasamiEquation_unique_of_exists_gamma
    (n k kInv : ℕ) (a : Fin 2)
    (hn : 0 < n) (hk : 0 < k) (hkn : k < n)
    (hInvPos : 0 < kInv) (hInvLt : kInv < n)
    (hcop : Nat.Coprime k n)
    (hInv : k * kInv ≡ 1 [MOD n])
    (hparity : kInv + a.val * n ≡ 1 [MOD 2])
    (c x y : GF n) (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hgamma : ∃ gamma : GF n, c = gamma ^ (2 ^ k + 1) + gamma)
    (hx : c * x ^ (2 ^ k + 1) = equationRHS n k kInv a x)
    (hy : c * y ^ (2 ^ k + 1) = equationRHS n k kInv a y) :
    x = y := by
  obtain ⟨gamma, hgamma⟩ := hgamma;
  by_cases hgamma0 : gamma = 0;
  · have := equationRHS_eq_zero_unique n k kInv a hn hInvPos hInv hparity x; have := equationRHS_eq_zero_unique n k kInv a hn hInvPos hInv hparity y; aesop;
  · obtain ⟨Delta, hDelta, hdef⟩ : ∃ Delta : GF n, Delta ≠ 0 ∧ IsDelta n k gamma Delta := exists_delta n k gamma hn hk hcop hgamma0 (by
    grind +suggestions);
    have hxy : (gammaPolynomial n k gamma).eval x = Delta⁻¹ ∧ (gammaPolynomial n k gamma).eval y = Delta⁻¹ := by
      have hxy : (ell n k c).eval x = 0 ∧ (ell n k c).eval y = 0 := by
        exact ⟨ kasamiEquation_implies_linearized n k kInv a hn hInvPos hInv c x hx0 hx, kasamiEquation_implies_linearized n k kInv a hn hInvPos hInv c y hy0 hy ⟩;
      have hxy : (gammaPolynomial n k gamma).eval x = 0 ∨ (gammaPolynomial n k gamma).eval x = Delta⁻¹ := by
        apply (ell_eval_eq_zero_iff_gammaPolynomial n k gamma Delta x hn hcop hgamma0 hDelta hdef).mp;
        unfold gammaCoefficient; aesop;
      have hxy' : (gammaPolynomial n k gamma).eval y = 0 ∨ (gammaPolynomial n k gamma).eval y = Delta⁻¹ := by
        apply (ell_eval_eq_zero_iff_gammaPolynomial n k gamma Delta y hn hcop hgamma0 hDelta hdef).mp;
        unfold gammaCoefficient; aesop;
      have hxy : ¬(gammaPolynomial n k gamma).eval x = 0 := by
        apply kasamiEquation_not_gammaPolynomial_zero n k kInv a gamma x hn hgamma0 hInv hparity;
        aesop
      have hxy' : ¬(gammaPolynomial n k gamma).eval y = 0 := by
        apply kasamiEquation_not_gammaPolynomial_zero n k kInv a gamma y hn hgamma0 hInv hparity;
        aesop;
      grind;
    by_contra hxy_ne;
    have := e0_plus_e1_equals_one n k kInv a gamma Delta x y hn hcop hInv hgamma0 hDelta hdef hxy_ne hxy.1 hxy.2;
    have := eTerm_eq_zero_of_kasamiEquation n k kInv a gamma x (by
    aesop)
    have := eTerm_eq_zero_of_kasamiEquation n k kInv a gamma y (by
    aesop)
    simp_all +decide [ eTerm ]

/-
Under the odd-parity condition, the Kasami equation has at most one
admissible solution: for a nonzero right-hand-side value we consider nonzero
solutions, while for `c=0` the zero solution is included.  This qualification
is necessary because `z=0` satisfies the displayed equation for every `c`.
-/
lemma kasamiEquation_unique
    (n k kInv : ℕ) (a : Fin 2)
    (hn : 0 < n) (hk : 0 < k) (hkn : k < n)
    (hInvPos : 0 < kInv) (hInvLt : kInv < n)
    (hcop : Nat.Coprime k n)
    (hInv : k * kInv ≡ 1 [MOD n])
    (hparity : kInv + a.val * n ≡ 1 [MOD 2])
    (c x y : GF n)
    (hxAdm : c ≠ 0 → x ≠ 0) (hyAdm : c ≠ 0 → y ≠ 0)
    (hx : c * x ^ (2 ^ k + 1) = equationRHS n k kInv a x)
    (hy : c * y ^ (2 ^ k + 1) = equationRHS n k kInv a y) :
    x = y := by
  by_cases hc : c = 0;
  · substs hc; exact ( equationRHS_eq_zero_unique n k kInv a hn hInvPos hInv hparity x ( by simpa [ eq_comm ] using hx ) ) ▸ ( equationRHS_eq_zero_unique n k kInv a hn hInvPos hInv hparity y ( by simpa [ eq_comm ] using hy ) ) ▸ rfl;
  · by_cases hgamma : ∃ gamma : GF n, c = gamma ^ (2 ^ k + 1) + gamma;
    · apply kasamiEquation_unique_of_exists_gamma n k kInv a hn hk hkn hInvPos hInvLt hcop hInv hparity c x y (hxAdm hc) (hyAdm hc) hgamma hx hy;
    · apply linearized_unique_of_not_exists_gamma n k hn c x y hgamma;
      · convert kasamiEquation_implies_linearized n k kInv a hn hInvPos hInv c x ( hxAdm hc ) hx using 1;
      · convert kasamiEquation_implies_linearized n k kInv a hn hInvPos hInv c y ( hyAdm hc ) hy using 1

/-
The substantive (sufficient) direction of the generalized Kasami
criterion, obtained by applying uniqueness of solutions to each fiber.
-/
lemma parity_implies_permutation
    (n k kInv : ℕ) (a : Fin 2)
    (hn : 0 < n) (hk : 0 < k) (hkn : k < n)
    (hInvPos : 0 < kInv) (hInvLt : kInv < n)
    (hcop : Nat.Coprime k n)
    (hInv : k * kInv ≡ 1 [MOD n])
    (hparity : kInv + a.val * n ≡ 1 [MOD 2]) :
    IsPermutationPolynomial (genKasamiPol n k kInv a) := by
  -- We need to show that the genKasamiPol is injective.
  have h_inj : Function.Injective (fun x => (genKasamiPol n k kInv a).eval x) := by
    intro x y hxy;
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp_all +decide [ evaluation_eq_zero_iff_equation ];
    · convert kasamiEquation_unique n k kInv a hn hk hkn hInvPos hInvLt hcop hInv hparity 0 0 y _ _ _ _ <;> simp_all +decide [ evaluation_eq_eval ];
      · unfold equationRHS; simp +decide [ Finset.sum_range_succ', pow_succ' ] ;
      · convert hxy.symm using 1;
        · rw [ ← hxy, genKasamiPol ] ; norm_num [ Polynomial.eval_finset_sum ] ;
          unfold tracePolynomial; norm_num [ Polynomial.eval_finset_sum ] ;
        · convert evaluation_eq_zero_iff_equation n k kInv a y hn hkn |>.1 _ using 1;
          · unfold genKasamiPol; simp +decide [ Polynomial.eval_finset_sum ] ;
            unfold tracePolynomial; simp +decide [ Polynomial.eval_finset_sum ] ;
          · convert hxy.symm using 1;
            unfold genKasamiPol; simp +decide [ Polynomial.eval_finset_sum ] ;
            unfold tracePolynomial; simp +decide [ Polynomial.eval_finset_sum ] ;
    · have h_eq : equationRHS n k kInv a x = 0 := by
        have h_eq : Polynomial.eval x (genKasamiPol n k kInv a) = 0 := by
          convert evaluation_eq_zero_iff_equation n k kInv a 0 hn hkn using 1;
          unfold equationRHS; simp +decide [ Finset.sum_range_succ', pow_succ, mul_assoc, mul_left_comm, pow_mul' ] ;
          rw [ hxy ];
        convert evaluation_eq_zero_iff_equation n k kInv a x hn hkn |>.1 h_eq using 1;
      have := kasamiEquation_unique n k kInv a hn hk hkn hInvPos hInvLt hcop hInv hparity 0 x 0; simp_all +decide [ equationRHS ] ;
    · apply kasamiEquation_unique n k kInv a hn hk hkn hInvPos hInvLt hcop hInv hparity (Polynomial.eval x (genKasamiPol n k kInv a)) x y ; aesop;
      · lia;
      · convert evaluation_eq_iff_equation_of_ne_zero n k kInv a ( Polynomial.eval x ( genKasamiPol n k kInv a ) ) x hn hkn hx |>.1 rfl using 1;
      · have := evaluation_eq_iff_equation_of_ne_zero n k kInv a ( Polynomial.eval y ( genKasamiPol n k kInv a ) ) y hn hkn hy; aesop;
  exact ⟨ h_inj, Finite.injective_iff_surjective.mp h_inj ⟩

/-- **Generalized Kasami permutation criterion.**

If `kInv` is the representative in `{1, ..., n-1}` of the multiplicative
inverse of `k` modulo `n`, then `q_a` permutes `GF(2^n)` exactly when
`kInv + a*n` is odd. -/
theorem generalizedKasami_isPermutation_iff
    (n k kInv : ℕ) (a : Fin 2)
    (hn : 0 < n) (hk : 0 < k) (hkn : k < n)
    (hInvPos : 0 < kInv) (hInvLt : kInv < n)
    (hcop : Nat.Coprime k n)
    (hInv : k * kInv ≡ 1 [MOD n]) :
    IsPermutationPolynomial (genKasamiPol n k kInv a) ↔
      kInv + a.val * n ≡ 1 [MOD 2] := by
  constructor
  · exact permutation_implies_parity n k kInv a hn hk hkn hInvPos hInvLt hcop hInv
  · exact parity_implies_permutation n k kInv a hn hk hkn hInvPos hInvLt hcop hInv

/-- Equivalent formulation of the main result directly in terms of the
separately defined evaluation function. -/
theorem evaluation_bijective_iff
    (n k kInv : ℕ) (a : Fin 2)
    (hn : 0 < n) (hk : 0 < k) (hkn : k < n)
    (hInvPos : 0 < kInv) (hInvLt : kInv < n)
    (hcop : Nat.Coprime k n)
    (hInv : k * kInv ≡ 1 [MOD n]) :
    Function.Bijective (genKasamiEval n k kInv a) ↔
      kInv + a.val * n ≡ 1 [MOD 2] := by
  simpa [genKasamiEval, IsPermutationPolynomial] using
    generalizedKasami_isPermutation_iff n k kInv a hn hk hkn hInvPos hInvLt hcop hInv