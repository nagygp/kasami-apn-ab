import RequestProject.genkasamipol

open scoped BigOperators

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace GeneralizedKasami

/-- The generalized Muller–Cohen–Matthews polynomial from page 135 of
Dobbertin's paper.  The parameter `b : Fin 2` represents `β ∈ GF(2)`. -/
noncomputable def genMCMpol (n k : ℕ) (b : Fin 2) : Polynomial (GF n) :=
  ((∑ i ∈ Finset.range k, Polynomial.X ^ (2 ^ i)) +
      Polynomial.C (algebraMap (ZMod 2) (GF n) b) * tracePolynomial n) ^
      (2 ^ k + 1) *
    Polynomial.X ^ ((2 ^ n - 1) - 2 ^ k)

/-- The evaluation map of the generalized MCM polynomial. -/
noncomputable def genMCMeval (n k : ℕ) (b : Fin 2) : GF n → GF n :=
  fun x => (genMCMpol n k b).eval x

/-- Dobbertin's first transfer linear polynomial, regarded as a map on the
finite field. -/
noncomputable def psi_beta (n k : ℕ) (b : Fin 2) (x : GF n) : GF n :=
  (∑ i ∈ Finset.range k, x ^ (2 ^ i)) +
    algebraMap (ZMod 2) (GF n) b * (∑ i ∈ Finset.range n, x ^ (2 ^ i))

/-- Dobbertin's inverse transfer linear polynomial, regarded as a map on the
finite field. -/
noncomputable def phi_alpha (n k kInv : ℕ) (a : Fin 2) (x : GF n) : GF n :=
  (∑ i ∈ Finset.range kInv, x ^ (2 ^ (i * k))) +
    algebraMap (ZMod 2) (GF n) a * (∑ i ∈ Finset.range n, x ^ (2 ^ i))

@[simp] theorem genMCMeval_eq_eval (n k : ℕ) (b : Fin 2) :
    genMCMeval n k b = (genMCMpol n k b).eval := rfl

lemma genMCMeval_formula (n k : ℕ) (b : Fin 2) (x : GF n) :
    genMCMeval n k b x =
      (psi_beta n k b x) ^ (2 ^ k + 1) *
        x ^ ((2 ^ n - 1) - 2 ^ k) := by
          convert congr_arg ( fun p : Polynomial ( GF n ) => p.eval x ) ( show genMCMpol n k b = ( ( ∑ i ∈ Finset.range k, Polynomial.X ^ ( 2 ^ i ) ) + Polynomial.C ( algebraMap ( ZMod 2 ) ( GF n ) b ) * tracePolynomial n ) ^ ( 2 ^ k + 1 ) * Polynomial.X ^ ( ( 2 ^ n - 1 ) - 2 ^ k ) from rfl ) using 1;
          unfold psi_beta tracePolynomial; simp +decide [ Polynomial.eval_finset_sum ] ;

/-
The parity relations in the two halves of Theorem 4 are equivalent.
-/
lemma theorem4_parity_transfer
    (n k kInv nPrime : ℕ) (a b : Fin 2)
    (hprod : kInv * k = nPrime * n + 1)
    (hqpar : kInv + a.val * n ≡ 1 [MOD 2])
    (hppar : k + b.val * n ≡ 1 [MOD 2]) :
    (b.val ≡ nPrime + a.val * k [MOD 2]) ↔
      (a.val ≡ nPrime + b.val * kInv [MOD 2]) := by
        fin_cases a <;> fin_cases b <;> simp_all +decide [ Nat.ModEq ];
        · grind;
        · grind;
        · grind +splitImp

/-
Under Dobbertin's parity relation, the two transfer linear maps are
mutual inverses.
-/
lemma transfer_maps_inverse
    (n k kInv nPrime : ℕ) (a b : Fin 2)
    (hn : 0 < n)
    (hprod : kInv * k = nPrime * n + 1)
    (hqpar : kInv + a.val * n ≡ 1 [MOD 2])
    (hbeta : b.val ≡ nPrime + a.val * k [MOD 2]) :
    Function.LeftInverse (phi_alpha n k kInv a) (psi_beta n k b) ∧
      Function.LeftInverse (psi_beta n k b) (phi_alpha n k kInv a) := by
        -- By definition of $phi_alpha$ and $psi_beta$, we know that $phi_alpha n k kInv a (psi_beta n k b x) = x$ for all $x \in GF(2^n)$.
        have h_phi_psi : ∀ x : GF n, phi_alpha n k kInv a (psi_beta n k b x) = x := by
          intro x
          have h_eq : (∑ i ∈ Finset.range kInv, (∑ j ∈ Finset.range k, x ^ (2 ^ j) + algebraMap (ZMod 2) (GF n) b * (∑ j ∈ Finset.range n, x ^ (2 ^ j))) ^ (2 ^ (i * k))) + algebraMap (ZMod 2) (GF n) a * (∑ j ∈ Finset.range n, (∑ j_1 ∈ Finset.range k, x ^ (2 ^ j_1) + algebraMap (ZMod 2) (GF n) b * (∑ j_1 ∈ Finset.range n, x ^ (2 ^ j_1))) ^ (2 ^ j)) = x := by
            -- By expanding the double sum and using the periodicity of the Frobenius automorphism, we can simplify the expression.
            have h_double_sum : ∑ i ∈ Finset.range kInv, ∑ j ∈ Finset.range k, x ^ (2 ^ (i * k + j)) = x + nPrime * (∑ j ∈ Finset.range n, x ^ (2 ^ j)) := by
              have h_double_sum : ∑ i ∈ Finset.range (kInv * k), x ^ (2 ^ i) = x + nPrime * (∑ j ∈ Finset.range n, x ^ (2 ^ j)) := by
                have h_double_sum : ∀ m : ℕ, ∑ i ∈ Finset.range (m * n), x ^ (2 ^ i) = m * ∑ j ∈ Finset.range n, x ^ (2 ^ j) := by
                  intro m; induction m <;> simp_all +decide [ Nat.succ_mul, Finset.sum_range_add ] ;
                  grind +suggestions;
                simp_all +decide [ add_comm, Finset.sum_range_succ ];
                have h_frobenius : x ^ (2 ^ n) = x := by
                  convert gf_frobenius_pow_card n hn x using 1;
                refine' Nat.recOn nPrime _ _ <;> simp_all +decide [ pow_succ, pow_mul' ];
              convert h_double_sum using 1;
              induction' kInv with kInv ih;
              · norm_num;
              · induction' kInv + 1 with kInv ih <;> simp_all +decide [ Nat.succ_mul, Finset.sum_range_add ];
            -- By combining terms, we can factor out common factors and simplify the expression.
            have h_simplify : ∑ i ∈ Finset.range kInv, (∑ j ∈ Finset.range k, x ^ (2 ^ j) + algebraMap (ZMod 2) (GF n) b * ∑ j ∈ Finset.range n, x ^ (2 ^ j)) ^ (2 ^ (i * k)) = x + (nPrime + b.val * kInv) * ∑ j ∈ Finset.range n, x ^ (2 ^ j) := by
              have h_simplify : ∑ i ∈ Finset.range kInv, (∑ j ∈ Finset.range k, x ^ (2 ^ j) + algebraMap (ZMod 2) (GF n) b * ∑ j ∈ Finset.range n, x ^ (2 ^ j)) ^ (2 ^ (i * k)) = ∑ i ∈ Finset.range kInv, (∑ j ∈ Finset.range k, x ^ (2 ^ (i * k + j))) + ∑ i ∈ Finset.range kInv, (algebraMap (ZMod 2) (GF n) b * ∑ j ∈ Finset.range n, x ^ (2 ^ j)) := by
                have h_simplify : ∀ i ∈ Finset.range kInv, (∑ j ∈ Finset.range k, x ^ (2 ^ j) + algebraMap (ZMod 2) (GF n) b * ∑ j ∈ Finset.range n, x ^ (2 ^ j)) ^ (2 ^ (i * k)) = ∑ j ∈ Finset.range k, x ^ (2 ^ (i * k + j)) + algebraMap (ZMod 2) (GF n) b * ∑ j ∈ Finset.range n, x ^ (2 ^ j) := by
                  intro i hi
                  have h_frobenius : (∑ j ∈ Finset.range k, x ^ (2 ^ j)) ^ (2 ^ (i * k)) = ∑ j ∈ Finset.range k, x ^ (2 ^ (i * k + j)) := by
                    have h_frobenius : ∀ (s : Finset ℕ) (f : ℕ → GF n), (∑ j ∈ s, f j) ^ (2 ^ (i * k)) = ∑ j ∈ s, f j ^ (2 ^ (i * k)) := by
                      exact fun s f => sum_pow_char_pow 2 (i * k) s f;
                    convert h_frobenius ( Finset.range k ) ( fun j => x ^ 2 ^ j ) using 2 ; ring;
                  have h_frobenius : (∑ j ∈ Finset.range n, x ^ (2 ^ j)) ^ (2 ^ (i * k)) = ∑ j ∈ Finset.range n, x ^ (2 ^ j) := by
                    convert trace_sum_frobenius n ( i * k ) x hn using 1;
                  rw [ add_pow_char_pow, ‹ ( ∑ j ∈ Finset.range k, x ^ 2 ^ j ) ^ 2 ^ ( i * k ) = ∑ j ∈ Finset.range k, x ^ 2 ^ ( i * k + j ) ›, mul_pow, h_frobenius ];
                  cases Fin.exists_fin_two.mp ⟨ b, rfl ⟩ <;> simp_all +decide [ pow_succ' ];
                rw [ ← Finset.sum_add_distrib, Finset.sum_congr rfl h_simplify ];
              simp_all +decide [ Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, add_mul, mul_add, mul_assoc, mul_comm, mul_left_comm, Finset.sum_add_distrib ];
              fin_cases b <;> simp +decide [ add_assoc ];
            have h_trace : ∑ j ∈ Finset.range n, (∑ j_1 ∈ Finset.range k, x ^ (2 ^ j_1) + algebraMap (ZMod 2) (GF n) b * ∑ j_1 ∈ Finset.range n, x ^ (2 ^ j_1)) ^ (2 ^ j) = (k + b.val * n) * ∑ j ∈ Finset.range n, x ^ (2 ^ j) := by
              have h_trace : ∑ j ∈ Finset.range n, (∑ j_1 ∈ Finset.range k, x ^ (2 ^ j_1)) ^ (2 ^ j) = ∑ j_1 ∈ Finset.range k, ∑ j ∈ Finset.range n, x ^ (2 ^ (j + j_1)) := by
                rw [ Finset.sum_comm, Finset.sum_congr rfl ];
                intro i hi; induction' ( Finset.range k ) using Finset.induction <;> simp_all +decide [ pow_add, pow_mul, Finset.sum_range_succ ] ;
                simp_all +decide [ add_pow_char_pow, pow_right_comm ];
              have h_trace : ∑ j_1 ∈ Finset.range k, ∑ j ∈ Finset.range n, x ^ (2 ^ (j + j_1)) = k * ∑ j ∈ Finset.range n, x ^ (2 ^ j) := by
                have h_trace : ∀ j_1 ∈ Finset.range k, ∑ j ∈ Finset.range n, x ^ (2 ^ (j + j_1)) = ∑ j ∈ Finset.range n, x ^ (2 ^ j) := by
                  intros j_1 hj_1
                  have h_trace : ∑ j ∈ Finset.range n, x ^ (2 ^ (j + j_1)) = ∑ j ∈ Finset.range n, x ^ (2 ^ j) := by
                    have h_periodic : ∀ j, x ^ (2 ^ (j + n)) = x ^ (2 ^ j) := by
                      intros j
                      have h_periodic : x ^ (2 ^ n) = x := by
                        convert gf_frobenius_pow_card n hn x using 1;
                      simp +decide [ pow_add, pow_mul, h_periodic ];
                      rw [ ← pow_mul, mul_comm, pow_mul, h_periodic ]
                    have h_periodic : ∑ j ∈ Finset.range n, x ^ (2 ^ (j + j_1)) = ∑ j ∈ Finset.range (n + j_1), x ^ (2 ^ j) - ∑ j ∈ Finset.range j_1, x ^ (2 ^ j) := by
                      rw [ ← Finset.sum_range_add_sum_Ico _ ( show j_1 ≤ n + j_1 from Nat.le_add_left _ _ ) ] ; simp +decide [ Finset.sum_Ico_eq_sum_range ] ; ring;
                      ac_rfl;
                    rw [ h_periodic, Finset.sum_range_add ];
                    simp_all +decide [ add_comm n ];
                  exact h_trace;
                rw [ Finset.sum_congr rfl h_trace, Finset.sum_const, Finset.card_range, nsmul_eq_mul ];
              simp_all +decide [ add_mul, Finset.sum_add_distrib ];
              have h_trace : ∑ j ∈ Finset.range n, ((algebraMap (ZMod 2) (GF n)) b * ∑ j_1 ∈ Finset.range n, x ^ (2 ^ j_1)) ^ (2 ^ j) = (algebraMap (ZMod 2) (GF n)) b * n * ∑ j ∈ Finset.range n, x ^ (2 ^ j) := by
                have h_trace : ∀ j ∈ Finset.range n, ((algebraMap (ZMod 2) (GF n)) b * ∑ j_1 ∈ Finset.range n, x ^ (2 ^ j_1)) ^ (2 ^ j) = (algebraMap (ZMod 2) (GF n)) b * ∑ j_1 ∈ Finset.range n, x ^ (2 ^ j_1) := by
                  intro j hj
                  have h_trace : (∑ j_1 ∈ Finset.range n, x ^ (2 ^ j_1)) ^ (2 ^ j) = ∑ j_1 ∈ Finset.range n, x ^ (2 ^ j_1) := by
                    convert trace_sum_frobenius n j x hn using 1;
                  rw [ mul_pow, h_trace ];
                  fin_cases b <;> simp +decide [ pow_succ' ];
                rw [ Finset.sum_congr rfl h_trace ] ; norm_num ; ring;
              convert congr_arg₂ ( · + · ) ‹∑ j ∈ Finset.range n, ( ∑ j_1 ∈ Finset.range k, x ^ 2 ^ j_1 ) ^ 2 ^ j = ↑k * ∑ j ∈ Finset.range n, x ^ 2 ^ j› h_trace using 1;
              · simp +decide [ add_pow_char_pow, Finset.sum_add_distrib ];
              · fin_cases b <;> rfl;
            have h_coeff : (nPrime + b.val * kInv + a.val * (k + b.val * n)) ≡ 0 [MOD 2] := by
              simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
              grind;
            obtain ⟨ m, hm ⟩ := Nat.modEq_zero_iff_dvd.mp h_coeff;
            replace hm := congr_arg ( ( ↑ ) : ℕ → GF n ) hm ; simp_all +decide [ ← mul_assoc, ← add_mul ] ;
            simp_all +decide [ ← add_mul, ← eq_sub_iff_add_eq' ];
            convert congr_arg ( · * ∑ j ∈ Finset.range n, x ^ 2 ^ j ) hm using 1 ; ring;
            · fin_cases a <;> fin_cases b <;> simp +decide [ mul_assoc, mul_comm, mul_left_comm ];
            · grind;
          convert h_eq using 1;
        refine' ⟨ h_phi_psi, _ ⟩;
        have h_finite : Function.Bijective (psi_beta n k b) := by
          exact ⟨ fun x y hxy => by have := h_phi_psi x; have := h_phi_psi y; aesop, Finite.injective_iff_surjective.mp ( fun x y hxy => by have := h_phi_psi x; have := h_phi_psi y; aesop ) ⟩;
        exact fun x => by obtain ⟨ y, rfl ⟩ := h_finite.2 x; aesop;

/-
The Kasami numerator is the `2^k`-th power of the inverse transfer
map.
-/
lemma equationRHS_eq_phi_pow
    (n k kInv : ℕ) (a : Fin 2) (x : GF n)
    (hn : 0 < n) (hInvPos : 0 < kInv)
    (hInv : k * kInv ≡ 1 [MOD n]) :
    equationRHS n k kInv a x = (phi_alpha n k kInv a x) ^ (2 ^ k) := by
      unfold equationRHS phi_alpha; rw [ add_pow_char_pow ] ;
      rw [ show ( Finset.Icc 1 kInv : Finset ℕ ) = Finset.image ( fun i => i + 1 ) ( Finset.range kInv ) from ?_, Finset.sum_image ] <;> norm_num [ pow_add, pow_mul', Finset.mul_sum _ _ _, Finset.sum_mul ];
      · haveI := Fact.mk ( show Nat.Prime 2 by decide ) ; simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, pow_right_comm ] ;
        induction' ( Finset.range kInv ) using Finset.induction <;> simp_all +decide [ Finset.sum_range_succ, pow_succ, pow_mul ];
        · fin_cases a <;> simp +decide [ pow_succ, pow_mul ];
          convert trace_sum_frobenius n k x hn |> Eq.symm using 1;
        · simp_all +decide [ add_pow_char_pow, mul_pow ];
          simp_all +decide [ add_assoc, pow_right_comm ];
      · ext ( _ | i ) <;> aesop

/-
Away from zero, the MCM evaluation has its quotient form.
-/
lemma genMCMeval_eq_div
    (n k : ℕ) (b : Fin 2) (x : GF n)
    (hn : 0 < n) (hkn : k < n) (hx : x ≠ 0) :
    genMCMeval n k b x = (psi_beta n k b x) ^ (2 ^ k + 1) / x ^ (2 ^ k) := by
      convert genMCMeval_formula n k b x using 1;
      rw [ div_eq_mul_inv, inv_eq_of_mul_eq_one_right ];
      convert FiniteField.pow_card_sub_one_eq_one x hx using 1;
      rw [ ← pow_add, Nat.add_sub_of_le ];
      convert rfl;
      convert GaloisField.card 2 n;
      any_goals exact Fintype.ofFinite ( GF n );
      · simp +decide [ Fintype.card_eq_nat_card, hn.ne' ];
      · exact Nat.le_sub_one_of_lt ( pow_lt_pow_right₀ ( by decide ) hkn )

/-
The first functional identity in Theorem 4:
`q_α(ψ_β(x)) = P_β(x)⁻¹`.
-/
lemma genKasami_comp_psi_eq_genMCM
    (n k kInv nPrime : ℕ) (a b : Fin 2)
    (hn : 0 < n) (hkn : k < n)
    (hInvPos : 0 < kInv)
    (hprod : kInv * k = nPrime * n + 1)
    (hqpar : kInv + a.val * n ≡ 1 [MOD 2])
    (hbeta : b.val ≡ nPrime + a.val * k [MOD 2]) :
    genKasamiEval n k kInv a ∘ psi_beta n k b =
      (fun x => x⁻¹) ∘ genMCMeval n k b := by
        funext x;
        by_cases hx : x = 0 <;> simp_all +decide [ genMCMeval_eq_div ];
        · unfold psi_beta; simp +decide [ genKasamiPol, genMCMpol ] ;
          simp +decide [ Polynomial.eval_finset_sum, tracePolynomial ];
        · have h_eq : (genKasamiEval n k kInv a (psi_beta n k b x)) * (genMCMeval n k b x) = 1 := by
            have h_eq : (genKasamiEval n k kInv a (psi_beta n k b x)) * (psi_beta n k b x) ^ (2 ^ k + 1) = (phi_alpha n k kInv a (psi_beta n k b x)) ^ (2 ^ k) := by
              convert evaluation_eq_iff_equation_of_ne_zero n k kInv a ( genKasamiEval n k kInv a ( psi_beta n k b x ) ) ( psi_beta n k b x ) hn hkn _ using 1;
              · rw [ equationRHS_eq_phi_pow ];
                · grind;
                · lia;
                · linarith;
                · rw [ mul_comm, hprod ] ; norm_num [ Nat.ModEq, Nat.add_mod, Nat.mul_mod ];
              · have := transfer_maps_inverse n k kInv nPrime a b hn hprod hqpar hbeta;
                intro h; have := this.1 x; simp_all +decide ;
                unfold phi_alpha at this; simp_all +decide [ Finset.sum_range_succ' ] ;
            have h_eq : (phi_alpha n k kInv a (psi_beta n k b x)) ^ (2 ^ k) = x ^ (2 ^ k) := by
              have h_eq : phi_alpha n k kInv a (psi_beta n k b x) = x := by
                apply (transfer_maps_inverse n k kInv nPrime a b hn hprod hqpar hbeta).left x;
              rw [h_eq];
            have h_eq : genMCMeval n k b x = (psi_beta n k b x) ^ (2 ^ k + 1) / x ^ (2 ^ k) := by
              exact genMCMeval_eq_div n k b x hn hkn hx;
            rw [ h_eq, mul_div, div_eq_iff ] <;> simp_all +decide [ pow_add, pow_mul ];
          exact eq_inv_of_mul_eq_one_left h_eq

/-
The reverse functional identity in Theorem 4:
`P_β(φ_α(x)) = q_α(x)⁻¹`.
-/
lemma genMCM_comp_phi_eq_genKasami
    (n k kInv nPrime : ℕ) (a b : Fin 2)
    (hn : 0 < n) (hk : 0 < k) (hkn : k < n)
    (hInvPos : 0 < kInv) (hInvLt : kInv < n)
    (hcop : Nat.Coprime k n)
    (hprod : kInv * k = nPrime * n + 1)
    (hqpar : kInv + a.val * n ≡ 1 [MOD 2])
    (hbeta : b.val ≡ nPrime + a.val * k [MOD 2]) :
    genMCMeval n k b ∘ phi_alpha n k kInv a =
      (fun x => x⁻¹) ∘ genKasamiEval n k kInv a := by
        have := transfer_maps_inverse n k kInv nPrime a b hn hprod hqpar hbeta;
        have := genKasami_comp_psi_eq_genMCM n k kInv nPrime a b hn hkn hInvPos hprod hqpar hbeta;
        ext x; have := congr_fun this ( phi_alpha n k kInv a x ) ; simp_all +decide [ Function.LeftInverse, Function.RightInverse ] ;

/-
**Dobbertin, Theorem 4 (page 139).**

If `kInv*k = nPrime*n+1`, `q_a` has the permutation parity, and
`b = nPrime+a*k (mod 2)`, then the transfer linear polynomials `ψ_b` and
`φ_a` are inverse permutations.  They carry the generalized Kasami
permutation polynomial to the generalized MCM permutation polynomial and
back.  In particular both evaluation maps are bijective.
-/
theorem dobbertin_theorem4
    (n k kInv nPrime : ℕ) (a b : Fin 2)
    (hn : 0 < n) (hk : 0 < k) (hkn : k < n)
    (hInvPos : 0 < kInv) (hInvLt : kInv < n)
    (hcop : Nat.Coprime k n)
    (hprod : kInv * k = nPrime * n + 1)
    (hqpar : kInv + a.val * n ≡ 1 [MOD 2])
    (hbeta : b.val ≡ nPrime + a.val * k [MOD 2]) :
    Function.Bijective (psi_beta n k b) ∧
      Function.Bijective (phi_alpha n k kInv a) ∧
      genKasamiEval n k kInv a ∘ psi_beta n k b =
        (fun x => x⁻¹) ∘ genMCMeval n k b ∧
      genMCMeval n k b ∘ phi_alpha n k kInv a =
        (fun x => x⁻¹) ∘ genKasamiEval n k kInv a ∧
      IsPermutationPolynomial (genKasamiPol n k kInv a) ∧
      IsPermutationPolynomial (genMCMpol n k b) := by
        refine' ⟨ _, _, _, _, _, _ ⟩;
        any_goals exact parity_implies_permutation n k kInv a hn hk hkn hInvPos hInvLt hcop ( by rw [ mul_comm, hprod ] ; norm_num [ Nat.ModEq ] ) hqpar;
        · have := transfer_maps_inverse n k kInv nPrime a b hn hprod hqpar hbeta;
          exact ⟨ this.1.injective, this.2.surjective ⟩;
        · have := transfer_maps_inverse n k kInv nPrime a b hn hprod hqpar hbeta;
          exact ⟨ this.2.injective, this.1.surjective ⟩;
        · exact genKasami_comp_psi_eq_genMCM n k kInv nPrime a b hn hkn hInvPos hprod hqpar hbeta;
        · exact genMCM_comp_phi_eq_genKasami n k kInv nPrime a b hn hk hkn hInvPos hInvLt hcop hprod hqpar hbeta;
        · have h_bijective : Function.Bijective (genKasamiEval n k kInv a) := by
            apply parity_implies_permutation n k kInv a hn hk hkn hInvPos hInvLt hcop (by
            rw [ mul_comm, hprod ] ; norm_num [ Nat.ModEq, Nat.add_mod, Nat.mul_mod ]) hqpar;
          have h_bijective : Function.Bijective (genMCMeval n k b ∘ phi_alpha n k kInv a) := by
            rw [ genMCM_comp_phi_eq_genKasami ];
            any_goals assumption;
            refine' Function.Bijective.comp _ h_bijective;
            exact ⟨ fun x y hxy => by simpa using hxy, fun x => ⟨ x⁻¹, by simp +decide ⟩ ⟩;
          have h_bijective : Function.Surjective (genMCMeval n k b) := by
            exact h_bijective.2.of_comp;
          exact ⟨ Finite.injective_iff_surjective.mpr h_bijective, h_bijective ⟩

end GeneralizedKasami