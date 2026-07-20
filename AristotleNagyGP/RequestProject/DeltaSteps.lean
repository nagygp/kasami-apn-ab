import RequestProject.GammaSteps

open scoped BigOperators

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace GeneralizedKasami

/-- The defining equation for the element `Delta` in Steps (6)--(10).
It is written using inverses, so it also covers the notation `1 / Delta^(2^k-1)`
from the paper. -/
def IsDelta (n k : ℕ) (gamma Delta : GF n) : Prop :=
  (Delta ^ (2 ^ k - 1))⁻¹ = gamma ^ (2 ^ k - 1) + gamma⁻¹

/-
Step (6): under the nonvanishing assumptions implicit in the paper's
second case, an element satisfying the defining equation for `Delta` exists.
The extra conclusion `Delta ≠ 0` records what is required by the displayed
reciprocal equation.
-/
lemma exists_delta
    (n k : ℕ) (gamma : GF n)
    (hn : 0 < n) (hk : 0 < k) (hcop : Nat.Coprime k n)
    (hgamma : gamma ≠ 0)
    (hc : gamma ^ (2 ^ k + 1) + gamma ≠ 0) :
    ∃ Delta : GF n, Delta ≠ 0 ∧ IsDelta n k gamma Delta := by
  -- Since `gcd(k,n)=1`, we have `gcd(2^k-1,2^n-1)=1` via `Nat.pow_sub_one_gcd_pow_sub_one`.
  have h_gcd : Nat.gcd (2 ^ k - 1) (2 ^ n - 1) = 1 := by
    simp_all +decide [ Nat.Coprime ];
  obtain ⟨Delta, hDelta⟩ : ∃ Delta : GF n, Delta ^ (2 ^ k - 1) = (gamma ^ (2 ^ k - 1) + gamma⁻¹)⁻¹ := by
    have h_order : ∀ x : GF n, x ≠ 0 → ∃ y : GF n, y ^ (2 ^ k - 1) = x := by
      intro x hx_nonzero
      have h_order : x ^ (2 ^ n - 1) = 1 := by
        have h_order : ∀ x : (GaloisField 2 n)ˣ, x ^ (2 ^ n - 1) = 1 := by
          have h_order : Nat.card (GaloisField 2 n)ˣ = 2 ^ n - 1 := by
            rw [ Nat.card_units, GaloisField.card ] ; norm_num;
            linarith;
          simp +decide [ ← h_order ];
        simpa [ Units.ext_iff ] using h_order ( Units.mk0 x hx_nonzero );
      -- Since `gcd(2^k-1,2^n-1)=1`, there exists an integer `m` such that `m*(2^k-1) ≡ 1 (mod 2^n-1)`.
      obtain ⟨m, hm⟩ : ∃ m : ℕ, m * (2 ^ k - 1) ≡ 1 [MOD (2 ^ n - 1)] := by
        have := Nat.exists_mul_mod_eq_one_of_coprime h_gcd;
        rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.ModEq, mul_comm ];
        · exact ⟨ 0, by norm_num ⟩;
        · exact Exists.elim ( this ( lt_tsub_iff_left.mpr ( by linarith [ Nat.pow_le_pow_right two_pos ( show n + 1 + 1 ≥ 2 by linarith ) ] ) ) ) fun m hm => ⟨ m, by rw [ hm.2, Nat.mod_eq_of_lt ( lt_tsub_iff_left.mpr ( by linarith [ Nat.pow_le_pow_right two_pos ( show n + 1 + 1 ≥ 2 by linarith ) ] ) ) ] ⟩;
      use x ^ m;
      rw [ ← pow_mul, ← Nat.mod_add_div ( m * ( 2 ^ k - 1 ) ) ( 2 ^ n - 1 ), hm ];
      rcases u : 2 ^ n - 1 with ( _ | _ | u ) <;> simp_all +decide [ pow_add, pow_mul ];
    by_cases h : gamma ^ ( 2 ^ k - 1 ) + gamma⁻¹ = 0 <;> simp_all +decide [ add_eq_zero_iff_eq_neg ];
    exact Nat.sub_ne_zero_of_lt ( one_lt_pow₀ one_lt_two hk.ne' );
  refine' ⟨ Delta, _, _ ⟩ <;> simp_all +decide [ IsDelta ];
  intro h; simp_all +decide [ pow_succ' ] ;
  rcases x : 2 ^ k with ( _ | _ | k ) <;> simp_all +decide [ pow_succ' ];
  grobner

/-
Step (7): the defining equation for `Delta` is equivalent to the
Frobenius identity used in the remainder of the argument.
-/
lemma delta_frobenius_identity
    (n k : ℕ) (gamma Delta : GF n)
    (hgamma : gamma ≠ 0) (hDelta : Delta ≠ 0)
    (hdef : IsDelta n k gamma Delta) :
    Delta ^ (2 ^ k) = gamma * Delta + (gamma * Delta) ^ (2 ^ k) := by
  replace hdef := congr_arg ( fun x => x * Delta ^ ( 2 ^ k - 1 ) * gamma * Delta ) hdef ; simp_all +decide [ mul_comm, mul_left_comm ] ; ring;
  rw [ show 2 ^ k = 2 ^ k - 1 + 1 by rw [ Nat.sub_add_cancel ( Nat.one_le_pow _ _ zero_lt_two ) ] ] ; simp_all +decide [ pow_add, mul_assoc, mul_comm, mul_left_comm ] ; ring;
  grind

/-
Step (8): the equation `Q(x)=1/Delta` is transformed into a standard
linearized equation after scaling by `Delta`.
-/
lemma gammaPolynomial_eq_delta_inv_iff
    (n k : ℕ) (gamma Delta x : GF n)
    (hgamma : gamma ≠ 0) (hDelta : Delta ≠ 0)
    (hdef : IsDelta n k gamma Delta) :
    (gammaPolynomial n k gamma).eval x = Delta⁻¹ ↔
      x / Delta + (x / Delta) ^ (2 ^ k) =
        (gamma * Delta)⁻¹ + ((gamma * Delta) ^ 2)⁻¹ := by
  simp_all +decide [ gammaPolynomial, gammaCoefficient ];
  rw [ ← eq_comm ] ; have := delta_frobenius_identity n k gamma Delta hgamma hDelta hdef; simp_all +decide [ pow_add, mul_comm, div_eq_mul_inv ] ;
  field_simp [hgamma, hDelta] at *;
  rw [ show ( x / Delta ) ^ 2 ^ k = x ^ 2 ^ k / Delta ^ 2 ^ k by rw [ div_pow ] ] ; rw [ this ] ; ring_nf at * ;
  grind

/-
Step (9): the kernel of `x ↦ x^(2^k)+x` on `GF(2^n)` is exactly
`{0,1}` when `k` and `n` are coprime.
-/
lemma frobenius_add_eq_frobenius_add_iff
    (n k : ℕ) (x y : GF n)
    (hn : 0 < n) (hcop : Nat.Coprime k n)
    (hxy : x ^ (2 ^ k) + x = y ^ (2 ^ k) + y) :
    x = y ∨ x = y + 1 := by
  -- Since $z^{2^k} = z$, we have $z^{2^k - 1} = 1$ if $z \neq 0$.
  by_cases hz : x - y = 0;
  · exact Or.inl <| eq_of_sub_eq_zero hz;
  · have hz_pow : (x - y) ^ (2 ^ k - 1) = 1 := by
      have hz_pow : (x - y) ^ (2 ^ k) = x - y := by
        simp_all +decide [ sub_pow_char_pow ];
        grind;
      exact mul_left_cancel₀ hz <| by rw [ ← pow_succ', Nat.sub_add_cancel <| Nat.one_le_pow _ _ zero_lt_two ] ; aesop;
    -- Since $z^{2^k - 1} = 1$, the order of $z$ divides both $2^k - 1$ and $2^n - 1$.
    have h_order_divides : orderOf (x - y) ∣ Nat.gcd (2 ^ k - 1) (2 ^ n - 1) := by
      refine' Nat.dvd_gcd ( orderOf_dvd_iff_pow_eq_one.mpr hz_pow ) _;
      rw [ orderOf_dvd_iff_pow_eq_one ];
      have hz_pow_n : (x - y) ^ (2 ^ n) = x - y := by
        convert gf_frobenius_pow_card n hn ( x - y ) using 1;
      exact mul_left_cancel₀ hz <| by rw [ ← pow_succ', Nat.sub_add_cancel ( Nat.one_le_pow _ _ zero_lt_two ) ] ; aesop;
    simp_all +decide [ Nat.Coprime, Nat.Coprime.symm ];
    exact Or.inr ( eq_add_of_sub_eq' h_order_divides )

/-
Step (10): the absolute trace of `Delta` is zero.
-/
lemma trace_sum_delta_eq_zero
    (n k : ℕ) (gamma Delta : GF n)
    (hn : 0 < n) (hgamma : gamma ≠ 0)
    (hDelta : Delta ≠ 0) (hdef : IsDelta n k gamma Delta) :
    ∑ j ∈ Finset.range n, Delta ^ (2 ^ j) = 0 := by
  convert trace_sum_frobenius n k Delta hn using 1;
  · convert trace_sum_frobenius n k Delta hn |> Eq.symm using 1;
  · -- Rewrite the sum of Delta^(2^j) as a sum ofDelta^(2^j) and apply the periodicity property
    have h_period : ∑ j ∈ Finset.range n, Delta ^ (2 ^ (j + k)) = ∑ j ∈ Finset.range n, Delta ^ (2 ^ j) := by
      have h_period : ∀ j, Delta ^ (2 ^ (j + n)) = Delta ^ (2 ^ j) := by
        intro j;
        convert gf_frobenius_mod n ( j + n ) j Delta hn ( by simp +decide [ Nat.ModEq ] ) using 1;
      -- By periodicity, we can shift the indices of the sum.
      have h_shift : ∑ j ∈ Finset.range n, Delta ^ (2 ^ (j + k)) = ∑ j ∈ Finset.range (n + k), Delta ^ (2 ^ j) - ∑ j ∈ Finset.range k, Delta ^ (2 ^ j) := by
        rw [ ← Finset.sum_Ico_eq_sub _ ];
        · rw [ Finset.sum_Ico_eq_sum_range ] ; norm_num [ add_comm, add_left_comm, add_assoc ];
        · linarith;
      rw [ h_shift, Finset.sum_range_add ];
      simp_all +decide [ add_comm n, pow_add ];
    have h_trace : ∑ j ∈ Finset.range n, (gamma * Delta) ^ (2 ^ (j + k)) = ∑ j ∈ Finset.range n, (gamma * Delta) ^ (2 ^ j) := by
      convert trace_sum_frobenius n k ( gamma * Delta ) hn using 1;
      simp +decide [ pow_add, pow_mul ];
      induction' ( Finset.range n ) using Finset.induction <;> simp_all +decide;
      rw [ add_pow_char_pow ];
    have h_trace : ∑ j ∈ Finset.range n, Delta ^ (2 ^ (j + k)) = ∑ j ∈ Finset.range n, (gamma * Delta) ^ (2 ^ j) + ∑ j ∈ Finset.range n, (gamma * Delta) ^ (2 ^ (j + k)) := by
      rw [ ← Finset.sum_add_distrib ];
      refine' Finset.sum_congr rfl fun j hj => _;
      convert congr_arg ( · ^ 2 ^ j ) ( delta_frobenius_identity n k gamma Delta hgamma hDelta hdef ) using 1 <;> ring;
      rw [ add_pow_char_pow ] ; ring;
    grind +ring

end GeneralizedKasami