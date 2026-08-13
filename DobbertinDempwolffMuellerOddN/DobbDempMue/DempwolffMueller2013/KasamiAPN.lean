import Mathlib
import DobbDempMue.FiniteField.KasamiDefs
import DobbDempMue.FiniteField.FrobeniusMove
import DobbDempMue.DempwolffMueller2013.Thm32
import DobbDempMue.FiniteField.ExpArith
import DobbDempMue.FiniteField.FrobAlg

/-!
# Kasami APN Theorem

The Kasami function x^d on GF(2ⁿ), where d = 2^{2k} - 2^k + 1, is APN
(Almost Perfect Nonlinear) when n is odd, k is odd, 1 < k < n, and gcd(k,n) = 1.

## Proof strategy

The proof connects to the Dempwolff–Müller Theorem 3.2 via three layers:

1. **Key identity**: `(x+1)^d + x^d + 1 = L_k(x²+x)^{q+1} / (x²+x)^q`
2. **Decomposition**: Φ(u) = L_k(u)^{q+1}/u^q = (L_k(u)·u^{e'})^{q+1}
3. **Composition**: L_k(·)·(·)^{e'} bijective (Thm 3.2) ∘ y^{q+1} bijective (Gold)
-/

namespace KasamiAPN

open DempwolffMueller Finset BigOperators

set_option maxHeartbeats 1600000

/-
═══════════════════════════════════════════
Layer 1: Artin–Schreier identity
L_k(x²+x) = x^{2^k} + x
═══════════════════════════════════════════

The truncated trace applied to x²+x telescopes:
L_k(x²+x) = x^{2^k} + x.
Proof: L_k(x²+x) = L_k(x²) + L_k(x) = L_k(x)² + L_k(x) = x^{2^k} + x.
-/
lemma truncTrace_artin_schreier {F : Type*} [CommRing F] [CharP F 2]
    (k : ℕ) (x : F) :
    truncTrace k (x ^ 2 + x) = x ^ (2 ^ k) + x := by
  induction' k with k ih generalizing x <;> simp_all +decide [ truncTrace, pow_succ, pow_mul ];
  · rw [ ← two_smul F x, CharTwo.two_eq_zero, zero_smul ];
  · rw [ Finset.sum_range_succ, ih ];
    rw [ add_pow_char_pow, mul_pow ] ; ring_nf;
    simp +decide [ show ( 2 : F ) = 0 by exact CharP.cast_eq_zero F 2 ]

/-
═══════════════════════════════════════════
Layer 2: The key polynomial identity
((x+1)^d + x^d + 1) · (x²+x)^q = (x^q + x)^{q+1}
═══════════════════════════════════════════

The key identity connecting the Kasami differential to the truncated trace.
For d = 2^{2k} - 2^k + 1 and q = 2^k:
  ((x+1)^d + x^d + 1) · (x²+x)^q = (x^q + x)^{q+1}
-/
lemma kasami_key_identity {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : 0 < k) (hkn : k < n)
    (x : F) :
    ((x + 1) ^ (kasamiExp k) + x ^ (kasamiExp k) + 1) *
      (x ^ 2 + x) ^ (2 ^ k) =
    (x ^ (2 ^ k) + x) ^ (2 ^ k + 1) := by
  have h_expand : (x + 1) ^ (2 ^ (2 * k)) = x ^ (2 ^ (2 * k)) + 1 ∧ (x + 1) ^ (2 ^ k) = x ^ (2 ^ k) + 1 := by
    have h_expand : ∀ (a b : F) (m : ℕ), (a + b) ^ (2 ^ m) = a ^ (2 ^ m) + b ^ (2 ^ m) :=
      fun a b m => add_pow_char_pow (p := 2) (n := m) a b
    aesop;
  unfold kasamiExp;
  rw [ show 2 ^ ( 2 * k ) = 2 ^ k * 2 ^ k by ring, show 2 ^ k * 2 ^ k - 2 ^ k = 2 ^ k * ( 2 ^ k - 1 ) by rw [ Nat.mul_sub_left_distrib, Nat.mul_one ] ];
  simp_all +decide [ pow_add, pow_mul ];
  rw [ show ( x ^ 2 ^ k + 1 ) ^ ( 2 ^ k - 1 ) = ( x ^ 2 ^ k + 1 ) ^ ( 2 ^ k ) / ( x ^ 2 ^ k + 1 ) from ?_, show ( x ^ 2 ^ k ) ^ ( 2 ^ k - 1 ) = ( x ^ 2 ^ k ) ^ ( 2 ^ k ) / ( x ^ 2 ^ k ) from ?_ ];
  · by_cases hx : x = 0 <;> by_cases hx' : x ^ 2 ^ k + 1 = 0 <;> simp_all +decide [ add_mul, mul_assoc, mul_comm, mul_left_comm, pow_succ, pow_mul ];
    · grind;
    · simp_all +decide [ add_pow_char_pow, mul_pow, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ];
      field_simp [hx, hx']
      ring_nf;
      simp_all +decide [ show ( 2 : F ) = 0 by exact CharP.cast_eq_zero F 2 ];
  · by_cases hx : x ^ 2 ^ k = 0 <;> simp_all +decide [ pow_succ, mul_assoc ];
    · exact ne_of_gt ( Nat.sub_pos_of_lt ( one_lt_pow₀ one_lt_two hk.ne' ) );
    · rw [ eq_div_iff ( pow_ne_zero _ hx ), ← pow_succ, Nat.sub_add_cancel ( Nat.one_le_pow _ _ ( by decide ) ) ];
  · by_cases h : x ^ 2 ^ k + 1 = 0 <;> simp_all +decide [ pow_succ, mul_assoc, div_eq_mul_inv ];
    · exact ne_of_gt ( Nat.sub_pos_of_lt ( one_lt_pow₀ one_lt_two hk.ne' ) );
    · field_simp;
      rw [ ← pow_succ', Nat.sub_add_cancel ( Nat.one_le_pow _ _ ( by decide ) ) ]

/-
═══════════════════════════════════════════
Layer 3: Gold coprimality
gcd(2^k + 1, 2^n - 1) = 1
═══════════════════════════════════════════

When gcd(k,n) = 1 and n is odd, gcd(2^k+1, 2^n-1) = 1.
-/
lemma gold_coprime {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hcop : Nat.Coprime k n) (hn_odd : Odd n) :
    Nat.Coprime (2 ^ k + 1) (2 ^ n - 1) := by
  -- Since $2^k + 1$ divides $2^{2k} - 1$, we have $\gcd(2^k + 1, 2^n - 1) \mid \gcd(2^{2k} - 1, 2^n - 1)$.
  have h_divides : Nat.gcd (2 ^ k + 1) (2 ^ n - 1) ∣ Nat.gcd (2 ^ (2 * k) - 1) (2 ^ n - 1) := by
    exact Nat.dvd_gcd ( dvd_trans ( Nat.gcd_dvd_left _ _ ) ( by use 2 ^ k - 1; rw [ ← Nat.sq_sub_sq ] ; ring_nf ) ) ( Nat.gcd_dvd_right _ _ );
  -- Since $\gcd(k, n) = 1$ and $n$ is odd, we have $\gcd(2k, n) = \gcd(2, n) \cdot \gcd(k, n) = 1$.
  have h_gcd_2k_n : Nat.gcd (2 * k) n = 1 := by
    exact Nat.Coprime.mul_left ( Nat.prime_two.coprime_iff_not_dvd.mpr <| by simpa [ ← even_iff_two_dvd, parity_simps ] using hn_odd ) hcop;
  simp_all +decide [ Nat.Coprime, Nat.Coprime.gcd_eq_one ]

/-
y^{2^k+1} is bijective on GF(2^n) when gcd(k,n)=1, n odd.
-/
lemma gold_pow_bijective {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : 0 < k) (hn_pos : 0 < n)
    (hcop : Nat.Coprime k n) (hn_odd : Odd n) :
    Function.Bijective (fun y : F => y ^ (2 ^ k + 1)) := by
  apply pow_field_bijective;
  · rw [ Nat.coprime_comm ];
    convert gold_coprime hk hn_pos hcop hn_odd using 1;
    rw [ hn ];
  · positivity

/-
═══════════════════════════════════════════
Layer 4: Arithmetic identity
═══════════════════════════════════════════

The key arithmetic identity connecting Kasami to Thm 3.2's k' transfer.
-/
lemma kasami_arith_identity {k n : ℕ} (hk : 1 < k) (hn : 1 < n) (hkn : k < n) :
    ((2 ^ (n - 1) - 2 ^ (k - 1) - 1) * (2 ^ n - 1 - 2 ^ k)) % (2 ^ n - 1) =
    (2 ^ (k - 1) * (2 ^ k + 1)) % (2 ^ n - 1) := by
  zify [ Int.ofNat_sub ( show 2 ^ n ≥ 1 from one_le_pow₀ ( by decide ) ) ];
  rcases n with ( _ | _ | n ) <;> rcases k with ( _ | _ | k ) <;> norm_num [ pow_succ' ] at *;
  rw [ Nat.cast_sub, Nat.cast_sub ] <;> norm_num <;> ring_nf;
  · rw [ Nat.sub_sub, Nat.cast_sub ] <;> norm_num ; ring_nf;
    · rw [ Int.emod_eq_emod_iff_emod_sub_eq_zero ] ; ring_nf ; norm_num;
      exact ⟨ 2 * 2 ^ n - 2 ^ k * 4 - 1, by ring ⟩;
    · linarith [ pow_pos ( by decide : 0 < 2 ) k, pow_lt_pow_right₀ ( by decide : 1 < 2 ) hkn ];
  · exact pow_le_pow_right₀ ( by decide ) hkn.le;
  · exact Nat.le_sub_of_add_le ( by nlinarith [ pow_pos ( by decide : 0 < 2 ) k, pow_lt_pow_right₀ ( by decide : 1 < 2 ) hkn ] )

/-
═══════════════════════════════════════════
Layer 5: Existence of the linking exponent e'
═══════════════════════════════════════════

There exists e' such that L_k(x)·x^{e'} is bijective (via LxXk'_bijective)
and e'·(2^k+1) ≡ 2^n-1-2^k (mod 2^n-1) (for the Φ decomposition).
-/
lemma exists_linking_exp {k n : ℕ} (hk : 1 < k) (hn : 1 < n) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hn_odd : Odd n) :
    ∃ e' : ℕ,
      (e' * (2 ^ k + 1)) % (2 ^ n - 1) = (2 ^ n - 1 - 2 ^ k) % (2 ^ n - 1) ∧
      ((2 ^ (n - 1) - 2 ^ (k - 1) - 1) * e') % (2 ^ n - 1) =
        2 ^ (k - 1) % (2 ^ n - 1) := by
  -- By definition of coprimality, there exists � an� e' such that e' * (2^k + 1)� � �2^n - 1 - 2^k (mod 2^n - 1).
  obtain ⟨e', he'⟩ : ∃ e', e' * (2 ^ k + 1) % (2 ^ n - 1) = (2 ^ n - 1 - 2 ^ k) % (2 ^ n - 1) := by
    -- By Euler's theorem, since gcd( �2�^k + 1, 2^n - 1) = � �1, we have (2^k + 1)^(φ(2^n - 1)) ≡ 1 (mod 2^n - 1).
    have h_euler : (2 ^ k + 1) ^ Nat.totient (2 ^ n - 1) ≡ 1 [MOD (2 ^ n - 1)] := by
      exact Nat.ModEq.pow_totient <| by simpa using gold_coprime ( by linarith ) ( by linarith ) hcop hn_odd;
    use (2 ^ n - 1 - 2 ^ k) * (2 ^ k + 1) ^ (Nat.totient (2 ^ n - 1) - 1);
    cases h : Nat.totient ( 2 ^ n - 1 ) <;> simp_all +decide [ pow_succ, mul_assoc ];
    rw [ Nat.ModEq.mul_left _ h_euler ];
    rw [ Nat.mul_one, Nat.mod_eq_of_lt ( Nat.sub_lt ( Nat.sub_pos_of_lt ( one_lt_pow₀ one_lt_two hn.ne_bot ) ) ( pow_pos ( by decide ) _ ) ) ];
  -- We need to show the second congruence � for� e'.
  have h2 : ((2 ^ (n - 1) - 2 ^ (k - 1) - 1) * e') * (2 ^ k + 1) ≡ 2 ^ (k - 1) * (2 ^ k + 1) [MOD 2 ^ n - 1] := by
    have h2 : ((2 ^ (n - 1) - 2 ^ (k - 1) - 1) * (2 ^ n - 1 - 2 ^ k)) % (2 ^ n - 1) = (2 ^ (k - 1) * (2 ^ k + 1)) % (2 ^ n - 1) := by
      exact kasami_arith_identity hk hn hkn;
    simpa only [ mul_assoc ] using Nat.ModEq.trans ( Nat.ModEq.mul_left _ he' ) h2;
  -- Since $2^k + 1$ � is� coprime to $2^n - 1$, we can divide both sides of the congruence by $2^k + 1$.
  have h3 : Nat.Coprime (2 ^ k + 1) (2 ^ n - 1) := by
    convert gold_coprime ( by linarith ) ( by linarith ) hcop hn_odd using 1;
  refine' ⟨ e', he', _ ⟩;
  rw [ Nat.ModEq.symm ];
  rw [ Nat.modEq_iff_dvd ] at *;
  refine' Int.dvd_of_dvd_mul_right_of_gcd_one _ _;
  exacts [ ↑ ( 2 ^ k + 1 ), by convert h2.neg_right using 1; push_cast; ring, by simpa [ Int.gcd, Int.natAbs ] using h3.symm ]

/-
═══════════════════════════════════════════
Layer 6: Φ is injective on units
═══════════════════════════════════════════

Φ(u) = L_k(u)^{q+1}/u^q is injective on GF(2^n)*.
Proof: Φ(u) = (L_k(u)·u^{e'})^{q+1}, composition of two bijections.
-/
lemma phi_injective_on_units {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (k : ℕ)
    (hk : 1 < k) (hk_odd : Odd k) (hkn : k < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime k n)
    {u v : F} (hu : u ≠ 0) (hv : v ≠ 0)
    (heq : truncTrace k u ^ (2 ^ k + 1) * v ^ (2 ^ k) =
           truncTrace k v ^ (2 ^ k + 1) * u ^ (2 ^ k)) :
    u = v := by
  -- By LxXk'_bijective, we know that � $�L_k(u)^{2k+1}/u^{2k} = L_k(v)^{2k+1}/v^{2k}$ implies $u = v$.
  obtain ⟨e', he'⟩ := exists_linking_exp hk (by linarith) hkn hcop hn_odd;
  -- By multiplying both sides of the equation by $u^{e' * (2^k + 1)}$ and $v^{e' * (2^k + 1)}$, we can simplify using the properties of exponents.
  have h_mul : (truncTrace k u * u ^ e') ^ (2 ^ k + 1) = (truncTrace k v * v ^ e') ^ (2 ^ k + 1) := by
    have h_mul : u ^ (e' * (2 ^ k + 1)) = u ^ (2 ^ n - 1 - 2 ^ k) ∧ v ^ (e' * (2 ^ k + 1)) = v ^ (2 ^ n - 1 - 2 ^ k) := by
      have h_mul : u ^ (2 ^ n - 1) = 1 ∧ v ^ (2 ^ n - 1) = 1 := by
        exact ⟨ by rw [ ← hn, FiniteField.pow_card_sub_one_eq_one u hu ], by rw [ ← hn, FiniteField.pow_card_sub_one_eq_one v hv ] ⟩;
      rw [ ← Nat.mod_add_div ( e' * ( 2 ^ k + 1 ) ) ( 2 ^ n - 1 ), ← Nat.mod_add_div ( 2 ^ n - 1 - 2 ^ k ) ( 2 ^ n - 1 ), he'.1 ] ; simp_all +decide [ pow_add, pow_mul ] ;
    simp_all +decide [ mul_pow, pow_mul' ];
    simp_all +decide [ mul_comm, pow_right_comm ];
    rw [ show u ^ ( 2 ^ n - 1 - 2 ^ k ) = u ^ ( 2 ^ n - 1 ) / u ^ ( 2 ^ k ) from ?_, show v ^ ( 2 ^ n - 1 - 2 ^ k ) = v ^ ( 2 ^ n - 1 ) / v ^ ( 2 ^ k ) from ?_ ];
    · rw [ show u ^ ( 2 ^ n - 1 ) = 1 from ?_, show v ^ ( 2 ^ n - 1 ) = 1 from ?_ ];
      · rw [ mul_one_div, mul_one_div, div_eq_div_iff ] <;> first | linear_combination' heq | simp +decide [ hu, hv ] ;
      · rw [ ← hn, FiniteField.pow_card_sub_one_eq_one v hv ];
      · rw [ ← hn, FiniteField.pow_card_sub_one_eq_one u hu ];
    · rw [ eq_div_iff ( pow_ne_zero _ hv ), ← pow_add, Nat.sub_add_cancel ( show 2 ^ k ≤ 2 ^ n - 1 from Nat.le_sub_one_of_lt ( pow_lt_pow_right₀ ( by decide ) hkn ) ) ];
    · rw [ eq_div_iff ( pow_ne_zero _ hu ), ← pow_add, Nat.sub_add_cancel ( show 2 ^ k ≤ 2 ^ n - 1 from Nat.le_sub_one_of_lt ( pow_lt_pow_right₀ ( by decide ) hkn ) ) ];
  -- By LxXk'_bijective, we know that $L_k(u) \cdot u^{e'} = L_k(v) \cdot v^{e'}$.
  have h_eq : truncTrace k u * u ^ e' = truncTrace k v * v ^ e' := by
    have := gold_pow_bijective hn k ( by linarith ) ( by linarith ) hcop hn_odd;
    exact this.injective h_mul;
  have := LxXk'_bijective hn k hk hk_odd hkn hcop e' he'.2; have := this.1; aesop;

/-
═══════════════════════════════════════════
Layer 7: Collision ⟹ u_x = u_y
═══════════════════════════════════════════

The Kasami differential collision forces x²+x = y²+y.
-/
lemma kasami_collision_forces_equal_u {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (k : ℕ)
    (hk : 0 < k) (hk_odd : Odd k) (hkn : k < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime k n)
    {x y : F}
    (hdiff : (x + 1) ^ (kasamiExp k) + x ^ (kasamiExp k) =
             (y + 1) ^ (kasamiExp k) + y ^ (kasamiExp k)) :
    x ^ 2 + x = y ^ 2 + y := by
  by_cases hk_one : k = 1
  · subst k
    have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
    have hthree : (3 : F) = 1 := by
      calc
        (3 : F) = (2 : F) + 1 := by norm_num
        _ = 1 := by rw [htwo, zero_add]
    simp only [kasamiExp] at hdiff
    ring_nf at hdiff
    simp only [htwo, hthree, mul_zero, mul_one, add_zero] at hdiff
    linear_combination hdiff
  · have hk_gt : 1 < k := by omega
    have h_eq : (x ^ (2 ^ k) + x) ^ (2 ^ k + 1) * (y ^ 2 + y) ^ (2 ^ k) = (y ^ (2 ^ k) + y) ^ (2 ^ k + 1) * (x ^ 2 + x) ^ (2 ^ k) := by
      have h_eq : ((x + 1) ^ (kasamiExp k) + x ^ (kasamiExp k) + 1) * (x ^ 2 + x) ^ (2 ^ k) = (x ^ (2 ^ k) + x) ^ (2 ^ k + 1) ∧ ((y + 1) ^ (kasamiExp k) + y ^ (kasamiExp k) + 1) * (y ^ 2 + y) ^ (2 ^ k) = (y ^ (2 ^ k) + y) ^ (2 ^ k + 1) := by
        exact ⟨ kasami_key_identity hn k ( by linarith ) ( by linarith ) x, kasami_key_identity hn k ( by linarith ) ( by linarith ) y ⟩;
      grind;
    by_cases hx : x ^ 2 + x = 0 <;> by_cases hy : y ^ 2 + y = 0;
    · rw [hx, hy];
    · have h_eq : (y ^ (2 ^ k) + y) ^ (2 ^ k + 1) = 0 := by
        have h_eq : (x + 1) ^ (kasamiExp k) + x ^ (kasamiExp k) + 1 = 0 := by
          have h_eq : x ^ 2 = x := by
            grind;
          have hchar : (1 : F) + 1 = 0 := by
            rw [ ← two_smul F 1, CharTwo.two_eq_zero, zero_smul ]
          cases eq_or_ne x 0 with
          | inl hx0 =>
              subst x
              simp [hchar, kasamiExp]
          | inr hx0 =>
              have hx1 : x = 1 := by
                apply mul_left_cancel₀ hx0
                simpa [pow_two] using h_eq
              subst x
              simp [hchar, kasamiExp]
        have := kasami_key_identity hn k ( by linarith ) ( by linarith ) y; simp_all +decide [ add_eq_zero_iff_eq_neg ] ;
      have h_eq : truncTrace k (y ^ 2 + y) = 0 := by
        rw [ truncTrace_artin_schreier ] ; aesop;
      exact absurd (truncTrace_ker_trivial hn k hk_odd (by linarith) (by linarith) hcop h_eq) hy;
    · have h_eq : (y + 1) ^ kasamiExp k + y ^ kasamiExp k = 1 := by
        have h_eq : y = 0 ∨ y = 1 := by
          grind +suggestions;
        rcases h_eq with ( rfl | rfl ) <;> simp_all +decide [ kasamiExp ];
      have h_eq : x ^ (2 ^ k) + x = 0 := by
        have h_eq : (x ^ (2 ^ k) + x) ^ (2 ^ k + 1) = 0 := by
          grind +suggestions;
        exact eq_zero_of_pow_eq_zero h_eq;
      have h_eq : truncTrace k (x ^ 2 + x) = 0 := by
        rw [ truncTrace_artin_schreier ] ; aesop;
      exact absurd ( truncTrace_ker_trivial hn k hk_odd ( by linarith ) ( by linarith ) hcop h_eq ) hx;
    · have := phi_injective_on_units hn k hk_gt hk_odd hkn hn_odd hcop hx hy ?_;
      · exact this;
      · rw [ truncTrace_artin_schreier, truncTrace_artin_schreier ] ; aesop

/-
═══════════════════════════════════════════
Layer 8: Structural lemmas
═══════════════════════════════════════════

u²+u = 0 in characteristic 2 iff u ∈ {0, 1}.
-/
lemma sq_add_self_eq_zero_char2 {F : Type*} [Field F] [CharP F 2] {u : F} :
    u ^ 2 + u = 0 ↔ u = 0 ∨ u = 1 := by
  grind +suggestions

/-
WLOG reduction: APN of `x^d` reduces to the normalized differential.  The
scaling `x ↦ x/a` turns the differential at `a` into the differential at `1`,
so no arithmetic hypotheses on `d` are needed.
-/
lemma apn_of_normalized {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (d : ℕ)
    (h_norm : ∀ (x y : F),
      (x + 1) ^ d + x ^ d = (y + 1) ^ d + y ^ d →
      y = x ∨ y = x + 1) :
    IsAPN (fun (x : F) => x ^ d) := by
  intro a ha x y hxy;
  convert h_norm ( x / a ) ( y / a ) _ |> Or.imp ( fun h => ?_ ) ( fun h => ?_ ) using 1 <;> simp_all +decide;
  · grind;
  · convert congr_arg ( · / a ^ d ) hxy using 1 <;> simp +decide [ add_div ];
    · rw [ div_add_one ha, div_pow, div_pow ];
    · rw [ ← div_pow, ← div_pow, div_add_one ha ]

-- ═══════════════════════════════════════════
-- Layer 9: Main theorem
-- ═══════════════════════════════════════════

/-- **Kasami APN Theorem.** Let F = GF(2ⁿ) with n odd. Let k be odd with
1 < k < n and gcd(k,n) = 1. Then f(x) = x^d where d = 2^{2k} - 2^k + 1
is APN on F.

The proof uses the Dempwolff–Müller Theorem 3.2 (LxXk'_bijective) as its core
engine, connecting the Kasami differential to the truncated trace via the
key identity and decomposing the resulting map as a composition of two bijections. -/
theorem kasami_is_apn_odd_n_odd_k {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (k : ℕ)
    (hk : 0 < k) (hk_odd : Odd k) (hkn : k < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime k n) :
    IsAPN (fun (x : F) => x ^ (kasamiExp k)) := by
  apply apn_of_normalized
  intro x y hdiff
  have hu : x ^ 2 + x = y ^ 2 + y :=
    kasami_collision_forces_equal_u hn k (by linarith) hk_odd hkn hn_odd hcop hdiff
  -- x²+x = y²+y means (x+y)²+(x+y) = 0
  have h_sum_zero : (x + y) ^ 2 + (x + y) = 0 := by
    have h2 : (x + y) ^ 2 = x ^ 2 + y ^ 2 := add_pow_char (R := F) (p := 2) x y
    rw [h2]
    have : x ^ 2 + y ^ 2 + (x + y) = (x ^ 2 + x) + (y ^ 2 + y) := by ring
    rw [this, hu, CharTwo.add_self_eq_zero]
  rw [sq_add_self_eq_zero_char2] at h_sum_zero
  rcases h_sum_zero with h | h
  · left
    have := neg_eq_of_add_eq_zero_left h
    rwa [CharTwo.neg_eq] at this
  · right
    have : y = x + y + x := by
      rw [add_comm x y, add_assoc]; simp [CharTwo.add_self_eq_zero]
    rwa [h, add_comm] at this

/--
Kasami APN for odd `n` and even `k`: reduce from `k` to `n-k` via Frobenius.

Assume `n` odd, `k` even, `1 < k < n`, and `gcd(k,n)=1`. Then
`x ↦ x^(2^(2k)-2^k+1)` is APN on `GF(2^n)`.
-/
theorem kasami_is_apn_odd_n_even_k {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (k : ℕ)
    (hk : 0 < k) (hk_even : Even k) (hkn : k < n) (hnk : 0 < n - k)
    (hn_odd : Odd n) (hcop : Nat.Coprime k n) :
    IsAPN (fun (x : F) => x ^ (kasamiExp k)) := by
  have hkn_le : k ≤ n := Nat.le_of_lt hkn
  have hnk_odd : Odd (n - k) := Nat.Odd.sub_even hkn_le hn_odd hk_even
  have hcop_nk_n : Nat.Coprime (n - k) n :=
    (Nat.coprime_self_sub_left hkn_le).2 hcop
  have hnk_lt_n : n - k < n := by omega
  have h_apn_nk : IsAPN (fun (x : F) => x ^ (kasamiExp (n - k))) :=
    kasami_is_apn_odd_n_odd_k hn (n - k) hnk hnk_odd hnk_lt_n hn_odd hcop_nk_n
  exact (kasami_apn_iff_complement (F := F) hn k hkn_le).2 h_apn_nk

theorem kasami_is_apn_odd_n {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (k : ℕ)
    (hk : 0 < k) (hkn : k < n) (hn_odd : Odd n) (hcop : Nat.Coprime k n) :
    IsAPN (fun (x : F) => x ^ (kasamiExp k)) := by
  by_cases hk_odd : Odd k
  · exact kasami_is_apn_odd_n_odd_k hn k hk hk_odd hkn hn_odd hcop
  · have hk_even : Even k := Nat.not_odd_iff_even.mp hk_odd
    exact kasami_is_apn_odd_n_even_k hn k hk hk_even hkn
      (Nat.sub_pos_of_lt hkn) hn_odd hcop

end KasamiAPN
