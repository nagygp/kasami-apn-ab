import RequestProject.DeltaSteps

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace GeneralizedKasami

/-
Statement (11): when `c = γ^(2^k+1)+γ` and `Delta` satisfies its
reciprocal equation, Dobbertin's affine linearized polynomial factors through
`Q(X) = c X^(2^k) + γ^2 X + γ`.
-/
theorem ell_eval_eq_gammaPolynomial_frobenius
    (n k : ℕ) (gamma Delta x : GF n)
    (hgamma : gamma ≠ 0) (hDelta : Delta ≠ 0)
    (hdef : IsDelta n k gamma Delta) :
    (ell n k (gammaCoefficient n k gamma)).eval x =
      ((gammaPolynomial n k gamma).eval x) ^ (2 ^ k) +
        (Delta ^ (2 ^ k - 1))⁻¹ * (gammaPolynomial n k gamma).eval x := by
  unfold ell gammaPolynomial gammaCoefficient;
  simp_all +decide [ IsDelta, pow_add, pow_mul' ];
  have h_frobenius : ∀ (a b : GF n), (a + b) ^ (2 ^ k) = a ^ (2 ^ k) + b ^ (2 ^ k) := by
    exact fun a b => add_pow_expChar_pow a b 2 k;
  simp_all +decide [ mul_pow, pow_right_comm ];
  cases h : 2 ^ k <;> simp_all +decide [ pow_succ, pow_mul ] ; ring;
  grind

/-
Statement (12): the zero set in (11) is exactly the union of the zero
fiber and the `Delta⁻¹` fiber of `Q`.
-/
theorem ell_eval_eq_zero_iff_gammaPolynomial
    (n k : ℕ) (gamma Delta x : GF n)
    (hn : 0 < n) (hcop : Nat.Coprime k n)
    (hgamma : gamma ≠ 0) (hDelta : Delta ≠ 0)
    (hdef : IsDelta n k gamma Delta) :
    (ell n k (gammaCoefficient n k gamma)).eval x = 0 ↔
      (gammaPolynomial n k gamma).eval x = 0 ∨
        (gammaPolynomial n k gamma).eval x = Delta⁻¹ := by
  have := @ell_eval_eq_gammaPolynomial_frobenius n k gamma Delta x hgamma hDelta hdef; simp_all +decide [ IsDelta ] ;
  have h_order : ∀ u : GF n, u ^ (2 ^ k - 1) = Delta⁻¹ ^ (2 ^ k - 1) → u = Delta⁻¹ := by
    intro u hu
    have h_order : ∀ v : GF n, v ^ (2 ^ k - 1) = 1 → v = 1 := by
      intro v hv; have := @gf_frobenius_pow_card n hn v; simp_all +decide [ pow_mul ] ;
      -- Since $v^{2^k - 1} = 1$, we have that $v$ is a root of unity of order $2^k - 1$.
      have h_root_of_unity : v ^ (Nat.gcd (2 ^ k - 1) (2 ^ n - 1)) = 1 := by
        rw [ Nat.gcd_comm, pow_gcd_eq_one ];
        cases eq_or_ne v 0 <;> simp_all +decide [ pow_succ' ];
        · rcases k with ( _ | _ | k ) <;> norm_num [ Nat.pow_succ' ] at *;
          · aesop;
          · rw [ zero_pow ( Nat.sub_ne_zero_of_lt ( by linarith [ Nat.one_le_pow k 2 zero_lt_two ] ) ) ] at hv ; norm_num at hv;
        · exact mul_left_cancel₀ ‹_› <| by rw [ ← pow_succ', Nat.sub_add_cancel ( Nat.one_le_pow _ _ zero_lt_two ) ] ; aesop;
      simp_all +decide [ Nat.Coprime, Nat.Coprime.pow ];
    specialize h_order ( u * Delta ) ; simp_all +decide [ mul_pow, pow_right_comm ] ;
    exact eq_inv_of_mul_eq_one_left ( h_order ( by rw [ ← hdef, inv_mul_cancel₀ ( pow_ne_zero _ hDelta ) ] ) );
  by_cases h : gammaCoefficient n k gamma * x ^ 2 ^ k + gamma ^ 2 * x + gamma = 0 <;> simp +decide [ h ];
  constructor <;> intro H;
  · apply h_order;
    convert congr_arg ( fun y => y / ( gammaCoefficient n k gamma * x ^ 2 ^ k + gamma ^ 2 * x + gamma ) ) ( eq_neg_of_add_eq_zero_left H ) using 1 <;> norm_num [ h ];
    · rw [ eq_div_iff h, ← pow_succ, Nat.sub_add_cancel ( Nat.one_le_pow _ _ ( by decide ) ) ];
    · grind;
  · rw [ ← hdef, H ];
    rw [ show Delta⁻¹ ^ 2 ^ k = ( Delta⁻¹ ^ ( 2 ^ k - 1 ) ) * Delta⁻¹ by rw [ ← pow_succ, Nat.sub_add_cancel ( Nat.one_le_pow _ _ ( by decide ) ) ] ] ; ring;
    grind

end GeneralizedKasami