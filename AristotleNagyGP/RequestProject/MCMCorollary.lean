import RequestProject.genMCM

open scoped BigOperators

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace GeneralizedKasami

/-- The classical Muller–Cohen–Matthews polynomial
`z * (∑ i < k, z^(2^i-1))^(2^k+1)`. -/
noncomputable def MCMpolynomial (n k : ℕ) : Polynomial (GF n) :=
  Polynomial.X *
    (∑ i ∈ Finset.range k, Polynomial.X ^ (2 ^ i - 1)) ^ (2 ^ k + 1)

/-- The function induced by the MCM polynomial on `GF(2^n)`. -/
noncomputable def MCMeval (n k : ℕ) : GF n → GF n :=
  fun x => (MCMpolynomial n k).eval x

@[simp] theorem MCMeval_eq_eval (n k : ℕ) :
    MCMeval n k = (MCMpolynomial n k).eval := rfl

/-
Coprimality supplies a positive representative of the inverse of `k`
modulo `n`, together with its quotient in the Bézout identity.
-/
lemma exists_positive_inverse_coefficients
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (hkn : k < n)
    (hcop : Nat.Coprime k n) :
    ∃ kInv nPrime : ℕ,
      0 < kInv ∧ kInv < n ∧ kInv * k = nPrime * n + 1 := by
  obtain ⟨kInv, hkInv⟩ : ∃ kInv, kInv * k ≡ 1 [MOD n] ∧ kInv < n ∧ 0 < kInv := by
    have := Nat.exists_mul_mod_eq_one_of_coprime hcop;
    rcases n with ( _ | _ | n ) <;> simp_all +decide [ mul_comm, Nat.ModEq ];
    exact ⟨ this.choose, this.choose_spec.2, this.choose_spec.1, Nat.pos_of_ne_zero fun h => by simpa [ h ] using this.choose_spec.2 ⟩;
  obtain ⟨ nPrime, hnPrime ⟩ := hkInv.1.symm.dvd;
  exact ⟨ kInv, nPrime.natAbs, hkInv.2.2, hkInv.2.1, by cases abs_cases nPrime <;> push_cast at * <;> nlinarith ⟩

/-
The displayed MCM polynomial and the `β = 0` generalized MCM
polynomial have the same evaluation function on `GF(2^n)`.
-/
theorem MCMeval_eq_genMCMeval_zero
    (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    MCMeval n k = genMCMeval n k (0 : Fin 2) := by
  funext x
  simp [MCMeval, genMCMeval, MCMpolynomial, genMCMpol];
  by_cases hx : x = 0 <;> simp_all +decide [ Polynomial.eval_finset_sum ];
  have h_exp : x ^ (2 ^ n - 1) = 1 := by
    have h_exp : x ^ (Nat.card (GF n) - 1) = 1 := by
      convert FiniteField.pow_card_sub_one_eq_one x hx using 1;
      convert rfl;
      convert Fintype.card_eq_nat_card;
      exact Fintype.ofFinite _;
    convert h_exp;
    rw [ GaloisField.card ];
    linarith;
  rw [ show ( ∑ i ∈ Finset.range k, x ^ 2 ^ i ) = x * ( ∑ i ∈ Finset.range k, x ^ ( 2 ^ i - 1 ) ) from ?_ ];
  · rw [ mul_pow ];
    rw [ show x ^ ( 2 ^ k + 1 ) = x * x ^ ( 2 ^ k ) by ring, show x ^ ( 2 ^ n - 1 - 2 ^ k ) = x ^ ( 2 ^ n - 1 ) / x ^ ( 2 ^ k ) by rw [ eq_div_iff ( pow_ne_zero _ hx ), ← pow_add, Nat.sub_add_cancel ( show 2 ^ k ≤ 2 ^ n - 1 from Nat.le_sub_one_of_lt ( pow_lt_pow_right₀ ( by decide ) hkn ) ) ] ] ; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
  · rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun i hi => by rw [ ← pow_succ', Nat.sub_add_cancel ( Nat.one_le_pow _ _ ( by decide ) ) ] ;

/-
**Muller–Cohen–Matthews corollary of Dobbertin's Theorem 4.**
If `n` and `k` are positive and coprime, `k < n`, and `k` is odd, then
`z * (∑ i < k, z^(2^i-1))^(2^k+1)` is a permutation polynomial over
`GF(2^n)`.
-/
theorem MCMpolynomial_isPermutation
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hkodd : Odd k) :
    IsPermutationPolynomial (MCMpolynomial n k) := by
  obtain ⟨kInv, nPrime, hkInv, hInvLt, hprod⟩ :=
    exists_positive_inverse_coefficients n k hn hk hkn hcop
  have h_perm : IsPermutationPolynomial (genMCMpol n k 0) := by
    apply (dobbertin_theorem4 n k kInv nPrime ⟨nPrime % 2, Nat.mod_lt _ (by decide)⟩ 0 hn hk hkn hkInv hInvLt hcop hprod (by
    replace hprod := congr_arg ( · % 2 ) hprod ; simp_all +decide [ Nat.add_mod, Nat.mul_mod, Nat.odd_iff.mp hkodd ] ;
    norm_num [ Nat.ModEq, Nat.add_mod, Nat.mul_mod, hprod ];
    cases Nat.mod_two_eq_zero_or_one nPrime <;> cases Nat.mod_two_eq_zero_or_one n <;> simp +decide only [*]) (by
    cases Nat.mod_two_eq_zero_or_one nPrime <;> simp_all +decide [Nat.ModEq];
    obtain ⟨ m, rfl ⟩ := hkodd; norm_num [ Nat.add_mod, Nat.mul_mod, ‹nPrime % 2 = _› ] ;)).right.right.right.right.right;
  have h_eval := MCMeval_eq_genMCMeval_zero n k hk hkn
  simp_all +decide [IsPermutationPolynomial]

end GeneralizedKasami