import Mathlib

open scoped BigOperators

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace GeneralizedKasami

/-- The canonical model of the field `GF(2^n)`. -/
abbrev GF (n : ℕ) := GaloisField 2 n

/-- The polynomial whose evaluation is the absolute trace polynomial
`z + z^2 + ... + z^(2^(n-1))`. -/
noncomputable def tracePolynomial (n : ℕ) : Polynomial (GF n) :=
  ∑ i ∈ Finset.range n, Polynomial.X ^ (2 ^ i)

/-- The generalized Kasami polynomial.  The parameter `a : Fin 2` represents
`α ∈ {0,1}`.  The inverse `kInv` is kept explicit, together with its defining
conditions in the main theorem. -/
noncomputable def genKasamiPol (n k kInv : ℕ) (a : Fin 2) : Polynomial (GF n) :=
  ((∑ i ∈ Finset.Icc 1 kInv, Polynomial.X ^ (2 ^ (i * k))) +
      Polynomial.C (algebraMap (ZMod 2) (GF n) a) * tracePolynomial n) *
    Polynomial.X ^ ((2 ^ n - 1) - (2 ^ k + 1))

/-- The function on `GF(2^n)` obtained by evaluating the generalized Kasami
polynomial.  This is deliberately separate from `genKasamiPol`. -/
noncomputable def genKasamiEval (n k kInv : ℕ) (a : Fin 2) : GF n → GF n :=
  fun x => (genKasamiPol n k kInv a).eval x

/-- A polynomial over a finite field is a permutation polynomial when its
associated evaluation function is bijective. -/
def IsPermutationPolynomial {F : Type*} [Semiring F] (p : Polynomial F) : Prop :=
  Function.Bijective p.eval

@[simp] theorem evaluation_eq_eval (n k kInv : ℕ) (a : Fin 2) :
    genKasamiEval n k kInv a = (genKasamiPol n k kInv a).eval := rfl

/-- The right-hand side of the equation used to analyze the fibers of the
Kasami evaluation map. -/
noncomputable def equationRHS (n k kInv : ℕ) (a : Fin 2) (z : GF n) : GF n :=
  (∑ i ∈ Finset.Icc 1 kInv, z ^ (2 ^ (i * k))) +
    algebraMap (ZMod 2) (GF n) a * (∑ i ∈ Finset.range n, z ^ (2 ^ i))

/-
Away from zero, a fiber equation for `q_a` is equivalent to the standard
Kasami equation `c z^(2^k+1) = RHS(z)`.
-/
lemma evaluation_eq_iff_equation_of_ne_zero
    (n k kInv : ℕ) (a : Fin 2) (c z : GF n)
    (hn : 0 < n) (hkn : k < n) (hz : z ≠ 0) :
    genKasamiEval n k kInv a z = c ↔
      c * z ^ (2 ^ k + 1) = equationRHS n k kInv a z := by
  unfold genKasamiEval equationRHS;
  unfold genKasamiPol;
  have hz_pow : z ^ (2 ^ n - 1) = 1 := by
    have hz_pow : z ^ (Nat.card (GF n) - 1) = 1 := by
      convert FiniteField.pow_card_sub_one_eq_one z hz;
      convert Nat.card_eq_fintype_card;
      exact Fintype.ofFinite _;
    convert hz_pow using 2;
    rw [ GaloisField.card ];
    linarith;
  by_cases h : 2 ^ n - 1 ≥ 2 ^ k + 1 <;> simp_all +decide [ Polynomial.eval_finset_sum ];
  · constructor <;> intro <;> simp_all +decide [ ← eq_div_iff, tracePolynomial ];
    · simp_all +decide [ Polynomial.eval_finset_sum ];
      rw [ div_div, ← pow_add, Nat.sub_add_cancel ( by linarith ), hz_pow, div_one ];
    · simp_all +decide [ Polynomial.eval_finset_sum, div_div, ← pow_add ];
  · rcases n with ( _ | _ | n ) <;> rcases k with ( _ | _ | k ) <;> norm_num [ Nat.pow_succ' ] at *;
    · fin_cases a <;> simp_all +decide [ tracePolynomial ]; all_goals exact eq_comm;
    · linarith [ Nat.one_le_pow n 2 zero_lt_two ];
    · linarith [ Nat.one_le_pow n 2 zero_lt_two ];
    · linarith [ pow_lt_pow_right₀ ( by decide : 1 < 2 ) hkn ]

/-
The zero fiber is represented by the same equation, including at `z=0`.
-/
lemma evaluation_eq_zero_iff_equation
    (n k kInv : ℕ) (a : Fin 2) (z : GF n)
    (hn : 0 < n) (hkn : k < n) :
    genKasamiEval n k kInv a z = 0 ↔ equationRHS n k kInv a z = 0 := by
  by_cases hz : z = 0 <;> simp_all +decide [ evaluation_eq_eval ];
  · unfold genKasamiPol; simp +decide [ Finset.sum_range_succ', Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] ;
    unfold tracePolynomial equationRHS; simp +decide [ Polynomial.eval_finset_sum ] ;
  · convert evaluation_eq_iff_equation_of_ne_zero n k kInv a 0 z hn hkn hz using 1 ; aesop

/-
The easy (necessary) direction: if the parity is even, evaluation at
`0` and `1` gives the same value.
-/
lemma permutation_implies_parity
    (n k kInv : ℕ) (a : Fin 2)
    (hn : 0 < n) (hk : 0 < k) (hkn : k < n)
    (hInvPos : 0 < kInv) (hInvLt : kInv < n)
    (hcop : Nat.Coprime k n)
    (hInv : k * kInv ≡ 1 [MOD n])
    (hperm : IsPermutationPolynomial (genKasamiPol n k kInv a)) :
    kInv + a.val * n ≡ 1 [MOD 2] := by
  -- By assumption, $q(0) = 0$ and $q(1) = 0$ if $kInv + a*n$ is even.
  by_contra h_contra
  have h_eq_zero : ((genKasamiPol n k kInv a).eval 0) = ((genKasamiPol n k kInv a).eval 1) := by
    unfold genKasamiPol;
    simp +decide [ Polynomial.eval_finset_sum, tracePolynomial ];
    fin_cases a <;> simp_all +decide [ Nat.ModEq ];
    · rw [ ← Nat.mod_add_div kInv 2, h_contra ] ; norm_num;
      grind +suggestions;
    · norm_cast;
      erw [ eq_comm, CharP.cast_eq_zero_iff ( GaloisField 2 n ) 2 ] ; norm_num [ Nat.dvd_iff_mod_eq_zero, h_contra ];
  have := hperm.1 h_eq_zero; simp_all +decide ;

/-
Frobenius is periodic with period `n` on `GF(2^n)`.
-/
lemma gf_frobenius_mod
    (n r s : ℕ) (x : GF n) (hn : 0 < n) (hrs : r ≡ s [MOD n]) :
    x ^ (2 ^ r) = x ^ (2 ^ s) := by
  -- By definition of exponentiation in finite fields, we know that $x^{2^n} = x$.
  have h_exp : ∀ x : GF n, x ^ (2 ^ n) = x := by
    have h_finite_field_pow : ∀ x : GaloisField 2 n, x ^ (Nat.card (GaloisField 2 n)) = x := by
      haveI := Fintype.ofFinite ( GaloisField 2 n );
      simp +decide [ FiniteField.pow_card ];
    rw [ GaloisField.card ] at h_finite_field_pow ; aesop;
    positivity;
  -- Since $r \equiv s \pmod{n}$, we can write $r = s + kn$ for some integer $k$.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, r = s + k * n ∨ s = r + k * n := by
    cases le_total r s <;> [ exact ⟨ ( s - r ) / n, Or.inr ( by nlinarith [ Nat.div_mul_cancel ( show n ∣ s - r from by rw [ ← Int.natCast_dvd_natCast ] ; simpa [ *, Nat.cast_sub ( show r ≤ s from by assumption ) ] using hrs.dvd ), Nat.sub_add_cancel ( show r ≤ s from by assumption ) ] ) ⟩ ; exact ⟨ ( r - s ) / n, Or.inl ( by nlinarith [ Nat.div_mul_cancel ( show n ∣ r - s from by rw [ ← Int.natCast_dvd_natCast ] ; simpa [ *, Nat.cast_sub ( show s ≤ r from by assumption ) ] using hrs.symm.dvd ), Nat.sub_add_cancel ( show s ≤ r from by assumption ) ] ) ⟩ ];
  rcases hk with ( rfl | rfl ) <;> simp_all +decide [ pow_add, pow_mul' ]; all_goals induction k <;> simp_all +decide [ pow_succ, pow_mul ]

/-
The absolute trace is fixed by every Frobenius automorphism.
-/
lemma trace_sum_frobenius
    (n k : ℕ) (x : GF n) (hn : 0 < n) :
    (∑ i ∈ Finset.range n, x ^ (2 ^ i)) ^ (2 ^ k) =
      ∑ i ∈ Finset.range n, x ^ (2 ^ i) := by
  induction' k with k ih;
  · norm_num;
  · have h_sum : x ^ (2 ^ n) = x := by
      have h_frobenius : x ^ (Nat.card (GF n)) = x := by
        haveI := Fintype.ofFinite ( GF n ) ; simp +decide [ FiniteField.pow_card ] ;
      convert h_frobenius using 1;
      rw [ GaloisField.card ];
      positivity;
    have h_sum : (∑ i ∈ Finset.range n, x ^ (2 ^ i)) ^ 2 = ∑ i ∈ Finset.range n, x ^ (2 ^ (i + 1)) := by
      simp +decide [ pow_succ, pow_mul, Finset.sum_mul _ _ _ ];
      simp +decide [ ← sq, ← Finset.sum_mul _ _ _ ];
      exact CharTwo.sum_sq (Finset.range n) fun i => x ^ 2 ^ i;
    have := Finset.sum_range_succ' ( fun i => x ^ 2 ^ i ) n; simp_all +decide [ pow_succ, pow_mul ] ;
    simp_all +decide [ Finset.sum_range_succ ]

/-
Raising the iterated Frobenius sum to `2^k` shifts its endpoints.
-/
lemma kasami_sum_frobenius
    (n k kInv : ℕ) (x : GF n) (hn : 0 < n)
    (hInvPos : 0 < kInv) (hInv : k * kInv ≡ 1 [MOD n]) :
    (∑ i ∈ Finset.Icc 1 kInv, x ^ (2 ^ (i * k))) ^ (2 ^ k) =
      (∑ i ∈ Finset.Icc 1 kInv, x ^ (2 ^ (i * k))) +
        x ^ (2 ^ k) + x ^ (2 ^ (k + 1)) := by
  -- Apply the Frobenius endomorphism to the sum.
  have h_frobenius : (∑ i ∈ Finset.Icc 1 kInv, x ^ (2 ^ (i * k))) ^ (2 ^ k) = ∑ i ∈ Finset.Icc 1 kInv, x ^ (2 ^ ((i + 1) * k)) := by
    induction' ( Finset.Icc 1 kInv : Finset ℕ ) using Finset.induction <;> simp_all +decide [ pow_add, pow_mul', Nat.succ_mul ];
    simp_all +decide [ add_pow_char_pow, pow_right_comm ];
  -- Reindex the sum on the right-hand side.
  have h_reindex : ∑ i ∈ Finset.Icc 1 kInv, x ^ (2 ^ ((i + 1) * k)) = ∑ i ∈ Finset.Icc 2 (kInv + 1), x ^ (2 ^ (i * k)) := by
    erw [ Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range ] ; norm_num [ add_comm, add_left_comm, add_assoc ];
  -- Use the fact that $k * kInv \equiv 1 \pmod{n}$ to simplify the exponent.
  have h_exp : x ^ (2 ^ ((kInv + 1) * k)) = x ^ (2 ^ (k + 1)) := by
    grind +suggestions;
  erw [ Finset.sum_Ico_eq_sub _ _, Finset.sum_Ico_eq_sub _ _ ] at * <;> norm_num at *;
  simp_all +decide [ Finset.sum_range_succ ];
  grind +qlia

/-- Dobbertin's affine linearized polynomial
`c^(2^k) X^(2^(2k)) + X^(2^k) + c X + 1`. -/
noncomputable def ell (n k : ℕ) (c : GF n) : Polynomial (GF n) :=
  Polynomial.C (c ^ (2 ^ k)) * Polynomial.X ^ (2 ^ (2 * k)) +
    Polynomial.X ^ (2 ^ k) + Polynomial.C c * Polynomial.X + 1

/-- The homogeneous linearized polynomial associated to `ell`.

This is `ell + 1`; since `GF(2^n)` has characteristic two, its expanded
form has no constant term. -/
noncomputable def ell_0 (n k : ℕ) (c : GF n) : Polynomial (GF n) :=
  ell n k c + 1

@[simp] lemma ell_eval (n k : ℕ) (c x : GF n) :
    (ell n k c).eval x =
      c ^ (2 ^ k) * x ^ (2 ^ (2 * k)) + x ^ (2 ^ k) + c * x + 1 := by
  unfold ell; norm_num;

@[simp] lemma ell_0_eval (n k : ℕ) (c x : GF n) :
    (ell_0 n k c).eval x =
      c ^ (2 ^ k) * x ^ (2 ^ (2 * k)) + x ^ (2 ^ k) + c * x := by
  unfold ell_0; simp +decide [ ell_eval ] ;
  grind

/-
Two inputs have the same value under `ell` exactly when their difference
is a root of the associated homogeneous polynomial `ell_0`.
-/
lemma ell_eval_eq_iff_ell_0_sub_eq_zero (n k : ℕ) (c x y : GF n) :
    (ell n k c).eval x = (ell n k c).eval y ↔
      (ell_0 n k c).eval (x - y) = 0 := by
  -- Use the properties of the Frobenius endomorphism and the characteristic of the field.
  have h_frob : ∀ a : GF n, a * a = a^2 := by
    exact fun a => by rw [ sq ] ;
  norm_num [ ell, ell_0, h_frob ] ; ring;
  -- In characteristic 2, we have $(x - y)^{2^r} = x^{2^r} + y^{2^r}$.
  have h_char_two : ∀ r : ℕ, ∀ x y : GF n, (x - y) ^ (2 ^ r) = x ^ (2 ^ r) + y ^ (2 ^ r) := by
    intro r x y; induction' r with r ih <;> simp_all +decide [ pow_succ, pow_mul ] ; ring;
    · exact CharTwo.sub_eq_add x y;
    · grind +ring;
  grind +ring

/-
Every solution of the Kasami equation satisfies Dobbertin's linearized
Equation (2).
-/
lemma kasamiEquation_implies_linearized
    (n k kInv : ℕ) (a : Fin 2)
    (hn : 0 < n) (hInvPos : 0 < kInv)
    (hInv : k * kInv ≡ 1 [MOD n])
    (c x : GF n) (hx0 : x ≠ 0)
    (hx : c * x ^ (2 ^ k + 1) = equationRHS n k kInv a x) :
    (ell n k c).eval x = 0 := by
  rw [ell_eval]
  have h_sub : (c * x ^ (2 ^ k + 1)) ^ (2 ^ k) + c * x ^ (2 ^ k + 1) = (equationRHS n k kInv a x) ^ (2 ^ k) + equationRHS n k kInv a x := by
    rw [hx];
  have h_rhs : (equationRHS n k kInv a x) ^ (2 ^ k) = equationRHS n k kInv a x + x ^ (2 ^ k) + x ^ (2 ^ (k + 1)) := by
    have h_rhs : (equationRHS n k kInv a x) ^ (2 ^ k) = (∑ i ∈ Finset.Icc 1 kInv, x ^ (2 ^ (i * k))) ^ (2 ^ k) + (algebraMap (ZMod 2) (GF n) a) * (∑ i ∈ Finset.range n, x ^ (2 ^ i)) ^ (2 ^ k) := by
      rw [ equationRHS ];
      simp +decide [ add_pow_char_pow, mul_pow ];
      fin_cases a <;> simp +decide [ pow_succ' ];
    rw [ h_rhs, kasami_sum_frobenius, trace_sum_frobenius ];
    · unfold equationRHS; ring;
    · grind +splitIndPred;
    · grind +splitIndPred;
    · linarith;
    · assumption;
  -- Combine like terms and simplify the equation.
  have h_simp : c ^ (2 ^ k) * x ^ (2 ^ (2 * k) + 2 ^ k) + c * x ^ (2 ^ k + 1) + x ^ (2 ^ k) + x ^ (2 ^ (k + 1)) = 0 := by
    convert sub_eq_zero.mpr h_sub using 1 ; ring;
    grind +qlia;
  refine' mul_left_cancel₀ ( pow_ne_zero ( 2 ^ k ) hx0 ) _;
  convert h_simp using 1 ; ring;
  norm_num

/-
Under odd parity, the right side of the Kasami equation vanishes only
at zero.
-/
lemma equationRHS_eq_zero_unique
    (n k kInv : ℕ) (a : Fin 2)
    (hn : 0 < n) (hInvPos : 0 < kInv)
    (hInv : k * kInv ≡ 1 [MOD n])
    (hparity : kInv + a.val * n ≡ 1 [MOD 2])
    (x : GF n) (hx : equationRHS n k kInv a x = 0) :
    x = 0 := by
  -- If $x^{2^k} = 1$, then $x$ is a root of unity of order $2^k$.
  by_cases hx_pow : x ^ (2 ^ k) = 1;
  · -- If $x$ is a root of unity of order $2^k$, then $x = 1$.
    have hx_one : x = 1 := by
      have h_order : x ^ (2 ^ n - 1) = 1 := by
        have h_order : x ≠ 0 := by
          rintro rfl; simp_all +decide [ pow_eq_zero_iff' ] ;
        convert FiniteField.pow_card_sub_one_eq_one x h_order using 1;
        convert rfl;
        convert GaloisField.card 2 n;
        swap;
        exact Fintype.ofFinite (GF n);
        simp +decide [ Fintype.card_eq_nat_card, hn.ne' ];
      -- Since $k * kInv \equiv 1 \pmod{n}$, we have $\gcd(2^k, 2^n - 1) = 1$.
      have h_coprime : Nat.gcd (2 ^ k) (2 ^ n - 1) = 1 := by
        exact Nat.Coprime.pow_left _ ( Nat.prime_two.coprime_iff_not_dvd.mpr <| by simpa [ ← even_iff_two_dvd, Nat.one_le_iff_ne_zero, parity_simps ] using hn.ne' );
      have := Nat.dvd_gcd ( orderOf_dvd_of_pow_eq_one hx_pow ) ( orderOf_dvd_of_pow_eq_one h_order ) ; aesop;
    simp_all +decide [ equationRHS ];
    simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
    convert hx using 1;
    erw [ ← map_natCast ( algebraMap ( ZMod 2 ) ( GF n ) ), ← map_natCast ( algebraMap ( ZMod 2 ) ( GF n ) ) ] ; norm_cast;
    fin_cases a <;> simp_all +decide [ Fin.val_add, Fin.val_mul ];
  · -- By `kasami_sum_frobenius` and `trace_sum_frobenius`, we have $x^{2^k} + x^{2^{k+1}} = 0$, which implies $x^{2^k}(x^{2^k} + 1) = 0$.
    have h_eq : x ^ (2 ^ k) * (x ^ (2 ^ k) + 1) = 0 := by
      have h_eq : (∑ i ∈ Finset.Icc 1 kInv, x ^ (2 ^ (i * k))) ^ (2 ^ k) + a.val * (∑ i ∈ Finset.range n, x ^ (2 ^ i)) ^ (2 ^ k) = 0 := by
        convert congr_arg ( · ^ ( 2 ^ k ) ) hx using 1;
        · unfold equationRHS; simp +decide [ add_pow_char_pow ] ;
          fin_cases a <;> simp +decide [ mul_pow ];
        · norm_num [ hn.ne' ];
      convert h_eq using 1;
      rw [ kasami_sum_frobenius n k kInv x hn hInvPos hInv, trace_sum_frobenius n k x hn ] ; ring;
      unfold equationRHS at hx; simp_all +decide [ pow_mul', Finset.sum_range_succ' ] ;
      simp_all +decide [ ← pow_mul, mul_comm ];
      fin_cases a <;> simp_all +decide [ add_eq_zero_iff_eq_neg ];
    cases eq_or_ne ( x ^ 2 ^ k ) 0 <;> simp_all +decide [ add_eq_zero_iff_eq_neg ];
    grind

/-
Every element of `GF(2^n)` is fixed by the `2^n`-th power map.
-/
lemma gf_frobenius_pow_card (n : ℕ) (hn : 0 < n) (u : GF n) :
    u ^ (2 ^ n) = u := by
  convert FiniteField.pow_card u;
  convert GaloisField.card 2 n;
  swap;
  apply_rules [ Fintype.ofFinite ];
  simp +decide [ hn.ne', Fintype.card_eq_nat_card ];
  exact eq_comm

/-
The formal factorization used in Dobbertin's first case.
-/
lemma ell_0_eval_factorization
    (n k : ℕ) (hn : 0 < n) (c z : GF n) (hc : c ≠ 0) :
    (ell_0 n k c).eval z =
      c⁻¹ *
        (((c * z ^ (2 ^ k - 1)) ^ (2 ^ (n - 1))) ^ (2 ^ k + 1) +
          (c * z ^ (2 ^ k - 1)) ^ (2 ^ (n - 1)) + c) ^ 2 * z := by
  -- Let $D = c \cdot z^{2^k-1}$ and $A = D^{2^{n-1}}$. Note that $A^2 = D^{2^n}$.
  set D : GF n := c * z ^ (2 ^ k - 1)
  set A : GF n := D ^ (2 ^ (n - 1))
  have hA2 : A ^ 2 = D := by
    have hA2 : A ^ 2 = D ^ (2 ^ n) := by
      rw [ ← pow_mul, ← pow_succ, Nat.sub_add_cancel hn ];
    rw [ hA2, gf_frobenius_pow_card n hn ];
  have h_expand : (A ^ (2 ^ k + 1) + A + c) ^ 2 = A ^ (2 * (2 ^ k + 1)) + A ^ 2 + c ^ 2 := by
    ring;
    grind +splitIndPred;
  simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, pow_succ, pow_mul ];
  simp +zetaDelta at *;
  field_simp [mul_comm, mul_assoc, mul_left_comm] at *;
  cases h : 2 ^ k <;> simp_all +decide [ pow_succ, mul_assoc, mul_comm, mul_left_comm ] ; ring

/-
If `c` is outside the image of `γ ↦ γ^(2^k+1)+γ`, Dobbertin's
linearized equation has at most one root.
-/
lemma linearized_unique_of_not_exists_gamma
    (n k : ℕ) (hn : 0 < n) (c x y : GF n)
    (hno : ¬ ∃ gamma : GF n, c = gamma ^ (2 ^ k + 1) + gamma)
    (hx : (ell n k c).eval x = 0)
    (hy : (ell n k c).eval y = 0) :
    x = y := by
  contrapose! hno; haveI := Fact.mk ( show Nat.Prime 2 by decide ) ;
  by_cases hc : c = 0;
  · exact ⟨ 0, by simp +decide [ hc ] ⟩;
  · grind +suggestions


end GeneralizedKasami
