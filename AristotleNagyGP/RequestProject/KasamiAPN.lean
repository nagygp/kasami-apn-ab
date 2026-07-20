import RequestProject.MCMCorollary

open scoped BigOperators

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace GeneralizedKasami

/-- The Kasami exponent `4^k - 2^k + 1`. -/
def kasamiExponent (k : ℕ) : ℕ := 4 ^ k - 2 ^ k + 1

/-- The Kasami monomial function on `GF(2^n)`. -/
noncomputable def kasami (n k : ℕ) : GF n → GF n := fun x => x ^ kasamiExponent k

/-- Every fiber of `f` contains at most two elements. -/
def AtMostTwo {α β : Type*} (f : α → β) : Prop :=
  ∀ ⦃x₁ x₂ x₃ : α⦄, f x₁ = f x₂ → f x₁ = f x₃ →
    x₁ = x₂ ∨ x₁ = x₃ ∨ x₂ = x₃

/-- The differential definition of an APN function. -/
def IsAPN {F : Type*} [Add F] [Zero F] (f : F → F) : Prop :=
  ∀ a ≠ 0, AtMostTwo (fun x => f x + f (x + a))

/-
Step (1): the arithmetic identity relating the complementary Kasami exponents.
-/
lemma kasamiExponent_complement_identity (n k : ℕ) (hkn : k ≤ n) :
    kasamiExponent (n - k) * 2 ^ (2 * k) =
      kasamiExponent k + (2 ^ n - 1) * (2 ^ n + 1 - 2 ^ k) := by
  zify [ Nat.pow_mul ];
  simp +decide [ kasamiExponent, hkn ];
  repeat rw [ Nat.cast_sub ] <;> push_cast;
  · rw [ show n = k + ( n - k ) by rw [ Nat.add_sub_cancel' hkn ] ] ; ring;
    norm_num [ pow_mul', ← mul_pow ] ; ring;
  · exact Nat.le_succ_of_le ( pow_le_pow_right₀ ( by decide ) hkn );
  · gcongr ; norm_num;
  · gcongr ; norm_num

/-
The exponent identity from Step (1), interpreted in `GF(2^n)`.
-/
lemma kasami_complement_frobenius (n k : ℕ) (hn : 0 < n) (hkn : k ≤ n)
    (x : GF n) :
    kasami n k x = (kasami n (n - k) x) ^ (2 ^ (2 * k)) := by
  by_cases hx : x = 0;
  · simp_all +decide [ kasami ];
    rcases k with ( _ | k ) <;> simp_all +decide [ kasamiExponent ];
  · have h_exp : x ^ (kasamiExponent (n - k) * 2 ^ (2 * k)) = x ^ (kasamiExponent k) := by
      have h_exp : x ^ (2 ^ n - 1) = 1 := by
        have h_order : x ^ (Nat.card (GF n) - 1) = 1 := by
          convert FiniteField.pow_card_sub_one_eq_one x hx;
          convert Nat.card_eq_fintype_card;
          exact Fintype.ofFinite _;
        convert h_order using 1;
        rw [ GaloisField.card ];
        positivity;
      rw [ kasamiExponent_complement_identity n k hkn ];
      simp_all +decide [ pow_add, pow_mul ];
    unfold kasami; simp_all +decide [ pow_mul' ] ;
    rw [ ← h_exp, pow_right_comm ]

/-
Postcomposition by a Frobenius power preserves the APN property.
-/
lemma isAPN_frobenius_post_iff (n r : ℕ) (f : GF n → GF n) :
    IsAPN (fun x => (f x) ^ (2 ^ r)) ↔ IsAPN f := by
  constructor <;> intro h a ha;
  · intro x₁ x₂ x₃ hx₁₂ hx₁₃;
    have := @h a ha ( x₁ ) ( x₂ ) ( x₃ ) ?_ ?_ <;> simp_all +decide [ add_pow_char_pow ];
    · rw [ ← add_pow_char_pow, hx₁₃, add_pow_char_pow ];
    · simp_all +decide [ ← add_pow_char_pow ];
  · intro x₁ x₂ x₃ hx₁ hx₂;
    convert h a ha _ _ using 1;
    · have h_frobenius : ∀ x y : GF n, (x + y) ^ (2 ^ r) = x ^ (2 ^ r) + y ^ (2 ^ r) := by
        haveI := Fact.mk ( show Nat.Prime 2 by decide ) ; simp +decide [ add_pow_char_pow ] ;
      have h_frobenius_inj : Function.Injective (fun x : GF n => x ^ (2 ^ r)) := by
        have h_frobenius_inj : ∀ x : GF n, x ^ (2 ^ r) = 0 → x = 0 := by
          aesop;
        intro x y hxy; specialize h_frobenius_inj ( x - y ) ; simp_all +decide [ sub_eq_iff_eq_add ] ;
        have := h_frobenius ( x - y ) y; simp_all +decide [ sub_eq_iff_eq_add ] ;
      exact h_frobenius_inj <| by aesop;
    · have h_frobenius : ∀ x y : GF n, (x + y) ^ (2 ^ r) = x ^ (2 ^ r) + y ^ (2 ^ r) := by
        haveI := Fact.mk ( show Nat.Prime 2 by decide ) ; simp +decide [ add_pow_char_pow ] ;
      have h_frobenius_inj : Function.Injective (fun x : GF n => x ^ (2 ^ r)) := by
        have h_frobenius_inj : ∀ x : GF n, x ^ (2 ^ r) = 0 → x = 0 := by
          aesop;
        intro x y hxy; specialize h_frobenius_inj ( x - y ) ; simp_all +decide [ sub_eq_iff_eq_add ] ;
        have := h_frobenius ( x - y ) y; simp_all +decide [ sub_eq_iff_eq_add ] ;
      exact h_frobenius_inj <| by aesop;

/-
Step (2): replacing `k` by `n-k` preserves the APN property.
-/
theorem kasami_isAPN_complement_iff (n k : ℕ) (hn : 0 < n) (hkn : k ≤ n) :
    IsAPN (kasami n k) ↔ IsAPN (kasami n (n - k)) := by
  convert isAPN_frobenius_post_iff n ( 2 * k ) _ using 1;
  congr! 2;
  convert kasami_complement_frobenius n k hn hkn _

/-
Scaling reduces every nonzero derivative of a monomial to its derivative at one.
-/
lemma monomial_isAPN_iff_derivative_one (n d : ℕ) :
    IsAPN (fun x : GF n => x ^ d) ↔
      AtMostTwo (fun x : GF n => x ^ d + (x + 1) ^ d + 1) := by
  unfold IsAPN;
  constructor <;> intro h x y z hxy hyz;
  · specialize h 1 ; aesop;
  · contrapose! h;
    intro H;
    have := @H ( z / x ) ( hxy / x ) ( hyz / x ) ?_ ?_ <;> simp_all +decide [ div_eq_iff, add_div ];
    · simp_all +decide [ ← eq_sub_iff_add_eq', mul_pow, mul_div_cancel₀, div_pow ];
      rw [ show z / x + 1 = ( z + x ) / x from by rw [ div_add_one y ], show hxy / x + 1 = ( hxy + x ) / x from by rw [ div_add_one y ] ] ; simp +decide [ *, div_pow, mul_pow ] ; ring;
    · have h_div : (z / x) ^ d + ((z + x) / x) ^ d = (hyz / x) ^ d + ((hyz + x) / x) ^ d := by
        simp_all +decide [ div_pow, ← add_div ];
        grind;
      convert h_div using 1 <;> simp +decide [ add_div, y ]

/-
Step (3): the APN criterion using the derivative at `1`.
-/
theorem kasami_isAPN_iff_derivative_one (n k : ℕ) :
    IsAPN (kasami n k) ↔
      AtMostTwo (fun x : GF n => kasami n k x + kasami n k (x + 1) + 1) := by
  convert monomial_isAPN_iff_derivative_one n ( kasamiExponent k ) using 1

/-
The telescoping Frobenius sum behind the MCM identity.
-/
lemma kasami_mcm_sum_telescopes (n k : ℕ) (x : GF n) :
    ∑ i ∈ Finset.range k, (x + x ^ 2) ^ (2 ^ i) = x + x ^ (2 ^ k) := by
  induction k <;> simp_all +decide [ Finset.sum_range_succ, pow_succ, pow_mul ];
  · grind +qlia;
  · simp_all +decide [ add_pow_char_pow ];
    ring;
    grind +qlia

/-
Multiplying the shifted MCM sum removes the decremented exponents.
-/
lemma kasami_mcm_shifted_sum (n k : ℕ) (x : GF n) :
    (x + x ^ 2) *
        (∑ i ∈ Finset.range k, (x + x ^ 2) ^ (2 ^ i - 1)) =
      x + x ^ (2 ^ k) := by
  rw [ Finset.mul_sum _ _ _ ];
  convert kasami_mcm_sum_telescopes n k x using 2;
  rw [ ← pow_succ', Nat.sub_add_cancel ( Nat.one_le_pow _ _ ( by decide ) ) ]

/-
Step (4): the Kasami derivative is the MCM polynomial evaluated at `x+x²`.
-/
theorem kasami_derivative_eq_MCM (n k : ℕ) (x : GF n) :
    kasami n k x + kasami n k (x + 1) + 1 =
      MCMeval n k (x + x ^ 2) := by
  have h_kasami_mcm : kasami n k x + kasami n k (x + 1) + 1 = (x + x ^ 2) * (∑ i ∈ Finset.range k, (x + x ^ 2) ^ (2 ^ i - 1)) ^ (2 ^ k + 1) := by
    have h_kasami_mcm : kasami n k x + kasami n k (x + 1) + 1 = (x + x ^ 2) * ((x + x ^ (2 ^ k)) / (x + x ^ 2)) ^ (2 ^ k + 1) := by
      by_cases hx : x + x ^ 2 = 0 <;> simp_all +decide [ kasami ];
      · -- Since $x + x^2 = 0$, we have $x = 0$ or $x = 1$.
        have hx_cases : x = 0 ∨ x = 1 := by
          grind;
        rcases hx_cases with ( rfl | rfl ) <;> norm_num [ kasamiExponent ];
        · grind +suggestions;
        · grind;
      · rw [ mul_comm, div_pow, div_mul_eq_mul_div, eq_div_iff ];
        · unfold kasamiExponent;
          rw [ show 4 ^ k - 2 ^ k = 2 ^ k * ( 2 ^ k - 1 ) by rw [ Nat.mul_sub_left_distrib ] ; ring_nf; norm_num [ pow_mul' ] ] ; ring;
          rw [ show ( 2 ^ k - 1 : ℕ ) * 2 ^ k = 2 ^ k * 2 ^ k - 2 ^ k by rw [ tsub_mul, one_mul ] ] ; rw [ pow_sub₀ ] <;> norm_num ; ring;
          · rw [ show ( 2 ^ ( k * 2 ) - 2 ^ k : ℕ ) = 2 ^ k * ( 2 ^ k - 1 ) by rw [ Nat.mul_sub_left_distrib ] ; ring ] ; rw [ pow_mul ] ; ring;
            rw [ show ( 2 ^ k - 1 : ℕ ) * 2 ^ k = 2 ^ ( 2 * k ) - 2 ^ k by rw [ tsub_mul, one_mul ] ; ring ] ; rw [ pow_sub₀ ] <;> norm_num ; ring;
            · by_cases hx : x = 0 <;> simp_all +decide [ pow_mul, pow_two, mul_assoc, mul_comm, mul_left_comm ];
              by_cases h : ( 1 + x ) ^ 2 ^ k = 0 <;> simp_all +decide [ pow_succ, mul_assoc, mul_comm, mul_left_comm ];
              · grind;
              · field_simp [hx, h]
                ring;
                simp +decide [ pow_mul, pow_two, mul_assoc, mul_comm, mul_left_comm, add_pow_char_pow ] ; ring;
                grind;
            · aesop;
            · exact pow_le_pow_right₀ ( by decide ) ( by linarith );
          · grind;
          · exact Nat.one_le_pow _ _ ( by decide );
        · exact pow_ne_zero _ hx;
    by_cases hx : x + x ^ 2 = 0 <;> simp_all +decide [ div_eq_mul_inv ];
    rw [ ← kasami_mcm_shifted_sum ];
    rw [ mul_right_comm, mul_inv_cancel₀ hx, one_mul ];
  unfold MCMeval MCMpolynomial;
  simp +decide [ h_kasami_mcm, Polynomial.eval_finset_sum ]

/-
In characteristic two, `x ↦ x+x²` has fibers of size at most two.
-/
lemma atMostTwo_artin_schreier (n : ℕ) :
    AtMostTwo (fun x : GF n => x + x ^ 2) := by
  intro x₁ x₂ x₃ h₁ h₂;
  grind +suggestions

/-
Injective postcomposition preserves the at-most-two-fibers property.
-/
lemma AtMostTwo.comp_of_injective {α β γ : Type*} {f : α → β} {g : β → γ}
    (hf : AtMostTwo f) (hg : Function.Injective g) :
    AtMostTwo (fun x => g (f x)) := by
  intro x₁ x₂ x₃ h₁ h₂;
  exact hf ( hg h₁ ) ( hg h₂ )

/-
Step (5): odd Kasami exponents are APN under the standard hypotheses.
-/
theorem kasami_isAPN_of_odd (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (hkn : k < n) (hcop : Nat.Coprime k n) (hkodd : Odd k) :
    IsAPN (kasami n k) := by
  -- Apply kasami_isAPN_iff_derivative_one. Rewrite the derivative pointwise with kasami_derivative_eq_MCM. The map x↦x+x² is AtMostTwo. MCMpolynomial_isPermutation gives bijectivity, hence injectivity, of MCMeval. Apply AtMostTwo.comp_of_injective.
  apply kasami_isAPN_iff_derivative_one n k |>.2;
  rw [ show ( fun x => kasami n k x + kasami n k ( x + 1 ) + 1 ) = fun x => MCMeval n k ( x + x ^ 2 ) from funext fun x => ?_ ];
  · convert atMostTwo_artin_schreier n |> fun h => h |> fun h => AtMostTwo.comp_of_injective h ?_ using 1;
    convert MCMpolynomial_isPermutation n k hn hk hkn hcop hkodd |> fun h => h.injective using 1;
  · exact kasami_derivative_eq_MCM n k x

/-
The Kasami monomial is APN for every positive coprime `k<n`.
-/
theorem kasami_isAPN (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (hkn : k < n) (hcop : Nat.Coprime k n) :
    IsAPN (kasami n k) := by
  by_cases hkodd : Odd k;
  · exact kasami_isAPN_of_odd n k hn hk hkn hcop hkodd
  · convert kasami_isAPN_complement_iff n k hn ( by linarith ) |> Iff.mpr <| ?_ using 1;
    convert kasami_isAPN_of_odd n ( n - k ) hn ( Nat.sub_pos_of_lt hkn ) ( Nat.sub_lt hn hk ) _ _ using 1;
    · simpa [ hkn.le ] using hcop;
    · cases le_iff_exists_add'.mp hkn.le ; simp_all +decide [ parity_simps ];
      exact Nat.odd_iff.mpr ( Nat.mod_two_ne_zero.mp fun h => by have := Nat.dvd_gcd ( even_iff_two_dvd.mp hkodd ) ( Nat.dvd_of_mod_eq_zero h ) ; aesop )

end GeneralizedKasami