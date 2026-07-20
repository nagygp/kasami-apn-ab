import RequestProject.genMCM

open scoped BigOperators

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace GeneralizedKasami

/-- The Kasami exponent $4^k - 2^k + 1$. -/
def kasamiExponent (k : ℕ) : ℕ := 4 ^ k - 2 ^ k + 1

/-- The Kasami monomial on `GF(2^n)`. -/
noncomputable def kasamiFunction (n k : ℕ) : GF n → GF n :=
  fun x => x ^ kasamiExponent k

/-- A function on `GF(2^n)` is APN when each nonzero derivative has fibers
of cardinality at most two. -/
noncomputable def IsAPN (n : ℕ) (f : GF n → GF n) : Prop := by
  classical
  letI := Fintype.ofFinite (GF n)
  exact ∀ a b : GF n, a ≠ 0 →
    (Finset.univ.filter fun x => f x + f (x + a) = b).card ≤ 2

/-- Complementary Kasami exponents differ by a multiple of `2^n - 1`. -/
lemma kasamiExponent_complement_identity
    (n k : ℕ) (hkn : k < n) :
    kasamiExponent (n - k) * 2 ^ (2 * k) =
      kasamiExponent k + (2 ^ n - 1) * (2 ^ n + 1 - 2 ^ k) := by
  have hfour : ∀ r : ℕ, 4 ^ r = 2 ^ (2 * r) := by
    intro r
    norm_num [show 4 = 2 ^ 2 by norm_num, pow_mul]
  have hpow : 2 ^ k ≤ 2 ^ n :=
    pow_le_pow_right₀ (by omega) (Nat.le_of_lt hkn)
  have hfour_le (r : ℕ) : 2 ^ r ≤ 4 ^ r := by
    rw [hfour]
    exact pow_le_pow_right₀ (by omega) (by omega)
  have hone (r : ℕ) : 1 ≤ 2 ^ r := by
    exact Nat.one_le_pow r 2 (by omega)
  apply Nat.cast_injective (R := ℤ)
  simp only [kasamiExponent, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat]
  rw [Nat.cast_sub (hfour_le (n - k)), Nat.cast_sub (hfour_le k),
    Nat.cast_sub (hone n), Nat.cast_sub (by omega : 2 ^ k ≤ 2 ^ n + 1)]
  rw [hfour, hfour]
  push_cast
  ring_nf
  have hdouble : (2 : ℤ) ^ ((n - k) * 2) * 2 ^ (k * 2) = 2 ^ (n * 2) := by
    rw [← pow_add]
    congr 1
    omega
  have hcross : (2 : ℤ) ^ (n - k) * 2 ^ k = 2 ^ n := by
    rw [← pow_add]
    congr 1
    omega
  have htriple : (2 : ℤ) ^ (n - k) * 2 ^ (k * 2) = 2 ^ n * 2 ^ k := by
    rw [show (k * 2 : ℕ) = k + k by omega, pow_add, ← mul_assoc, hcross]
  rw [hdouble, htriple]
  ring

/-- The Kasami monomial with complementary parameter differs by a Frobenius
power on `GF(2^n)`. -/
lemma kasamiFunction_complement_frobenius
    (n k : ℕ) (hn : 0 < n) (hkn : k < n) (x : GF n) :
    kasamiFunction n k x =
      (kasamiFunction n (n - k) x) ^ (2 ^ (2 * k)) := by
  unfold kasamiFunction
  rw [← pow_mul, kasamiExponent_complement_identity n k hkn, pow_add, pow_mul]
  by_cases hx : x = 0
  · subst x
    simp [kasamiExponent]
  · have hcard : x ^ (2 ^ n - 1) = 1 := by
      have hcard' : x ^ (Nat.card (GF n) - 1) = 1 := by
        convert FiniteField.pow_card_sub_one_eq_one x hx
        convert Nat.card_eq_fintype_card
        exact Fintype.ofFinite (GF n)
      convert hcard' using 2
      rw [GaloisField.card]
      linarith
    rw [hcard, one_pow, mul_one]

/-- Every Frobenius power is injective on a field of characteristic two. -/
lemma frobeniusPower_injective (n r : ℕ) :
    Function.Injective (fun x : GF n => x ^ (2 ^ r)) := by
  intro x y hxy
  have hzero : (x - y) ^ (2 ^ r) = 0 := by
    convert sub_eq_zero.mpr hxy using 1
    haveI := Fact.mk (show Nat.Prime 2 by decide)
    simp [sub_pow_char_pow]
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hzero)

/-- Postcomposition by a Frobenius power preserves the APN property. -/
lemma isAPN_frobeniusPower_iff (n r : ℕ) (f : GF n → GF n) :
    IsAPN n f ↔ IsAPN n (fun x => (f x) ^ (2 ^ r)) := by
  classical
  letI := Fintype.ofFinite (GF n)
  let frobenius : GF n → GF n := fun x => x ^ (2 ^ r)
  have hinj : Function.Injective frobenius := frobeniusPower_injective n r
  have hsurj : Function.Surjective frobenius :=
    Finite.injective_iff_surjective.mp hinj
  have hadd (u v : GF n) : frobenius (u + v) = frobenius u + frobenius v := by
    unfold frobenius
    haveI := Fact.mk (show Nat.Prime 2 by decide)
    rw [add_pow_char_pow]
  constructor
  · intro hf
    unfold IsAPN at hf ⊢
    intro a b ha
    obtain ⟨c, hc⟩ := hsurj b
    have hfilter :
        Finset.univ.filter (fun x => frobenius (f x) + frobenius (f (x + a)) = b) =
          Finset.univ.filter (fun x => f x + f (x + a) = c) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hc, ← hadd]
      exact hinj.eq_iff
    rw [hfilter]
    exact hf a c ha
  · intro hf
    unfold IsAPN at hf ⊢
    intro a b ha
    have hfilter :
        Finset.univ.filter (fun x => f x + f (x + a) = b) =
          Finset.univ.filter
            (fun x => frobenius (f x) + frobenius (f (x + a)) = frobenius b) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hadd]
      exact hinj.eq_iff.symm
    rw [hfilter]
    exact hf a (frobenius b) ha

/-- The Kasami monomials with parameters `k` and `n-k` are APN together. -/
lemma kasamiFunction_isAPN_iff_complement
    (n k : ℕ) (hn : 0 < n) (hkn : k < n) :
    IsAPN n (kasamiFunction n k) ↔ IsAPN n (kasamiFunction n (n - k)) := by
  have hfunction : kasamiFunction n k =
      fun x => (kasamiFunction n (n - k) x) ^ (2 ^ (2 * k)) := by
    funext x
    exact kasamiFunction_complement_frobenius n k hn hkn x
  rw [hfunction]
  exact (isAPN_frobeniusPower_iff n (2 * k) (kasamiFunction n (n - k))).symm

/-- The normalized derivative of the Kasami monomial. -/
noncomputable def kasamiNormalizedDerivative (n k : ℕ) : GF n → GF n :=
  fun x => kasamiFunction n k x + kasamiFunction n k (x + 1) + 1

/-- A map is two-to-one when every fiber has cardinality at most two. -/
noncomputable def IsTwoToOne (n : ℕ) (g : GF n → GF n) : Prop := by
  classical
  letI := Fintype.ofFinite (GF n)
  exact ∀ b : GF n, (Finset.univ.filter fun x => g x = b).card ≤ 2

lemma kasami_derivative_scale_iff
    (n k : ℕ) (a y b : GF n) (ha : a ≠ 0) :
    kasamiFunction n k (a * y) + kasamiFunction n k (a * y + a) = b ↔
      kasamiNormalizedDerivative n k y = b / kasamiFunction n k a + 1 := by
  have hpow : a ^ kasamiExponent k ≠ 0 := pow_ne_zero _ ha
  rw [show a * y + a = a * (y + 1) by ring]
  unfold kasamiNormalizedDerivative kasamiFunction
  rw [mul_pow, mul_pow]
  constructor
  · intro h
    apply add_right_cancel_iff.mpr
    apply (eq_div_iff hpow).2
    rw [mul_comm]
    simpa [mul_add] using h
  · intro h
    have hsum : y ^ kasamiExponent k + (y + 1) ^ kasamiExponent k =
        b / a ^ kasamiExponent k := by
      exact add_right_cancel_iff.mp h
    have hproduct :
        (y ^ kasamiExponent k + (y + 1) ^ kasamiExponent k) *
          a ^ kasamiExponent k = b := by
      exact (eq_div_iff hpow).1 hsum
    rw [mul_comm] at hproduct
    simpa [mul_add] using hproduct

/-- The Kasami monomial is APN exactly when its normalized derivative is
two-to-one. -/
theorem kasamiFunction_isAPN_iff_normalizedDerivative_twoToOne
    (n k : ℕ) :
    IsAPN n (kasamiFunction n k) ↔
      IsTwoToOne n (kasamiNormalizedDerivative n k) := by
  classical
  letI := Fintype.ofFinite (GF n)
  have hchar : (1 : GF n) + 1 = 0 := by
    norm_num
    erw [CharP.cast_eq_zero_iff (GaloisField 2 n) 2]
  have htwo : (2 : GF n) = 0 := by
    erw [CharP.cast_eq_zero_iff (GaloisField 2 n) 2]
  have hshift (u v : GF n) : u + 1 = v ↔ u = v + 1 := by
    constructor <;> intro h
    · calc
        u = u + 1 + 1 := by rw [add_assoc, hchar, add_zero]
        _ = v + 1 := by rw [h]
    · calc
        u + 1 = (v + 1) + 1 := by rw [h]
        _ = v := by rw [add_assoc, hchar, add_zero]
  constructor
  · intro hapn
    unfold IsAPN at hapn
    unfold IsTwoToOne
    intro b
    have hfilter :
        Finset.univ.filter (fun x => kasamiNormalizedDerivative n k x = b) =
          Finset.univ.filter
            (fun x => kasamiFunction n k x + kasamiFunction n k (x + 1) = b + 1) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      unfold kasamiNormalizedDerivative
      exact hshift _ _
    rw [hfilter]
    exact hapn 1 (b + 1) one_ne_zero
  · intro htwo
    unfold IsAPN
    intro a b ha
    let c : GF n := b / kasamiFunction n k a + 1
    have hmul_bijective : Function.Bijective (fun y : GF n => a * y) := by
      constructor
      · intro x y hxy
        exact mul_left_cancel₀ ha hxy
      · intro y
        refine ⟨a⁻¹ * y, ?_⟩
        field_simp
    have hcard :
        (Finset.univ.filter fun y => kasamiNormalizedDerivative n k y = c).card =
          (Finset.univ.filter fun x =>
            kasamiFunction n k x + kasamiFunction n k (x + a) = b).card := by
      apply Finset.card_bijective (fun y : GF n => a * y) hmul_bijective
      intro y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (kasami_derivative_scale_iff n k a y b ha).symm
    rw [← hcard]
    exact htwo c

lemma mcm_sum_at_quadratic (n k : ℕ) (x : GF n) :
    (∑ i ∈ Finset.range k, (x + x ^ 2) ^ (2 ^ i)) = x + x ^ (2 ^ k) := by
  haveI := Fact.mk (show Nat.Prime 2 by decide)
  have hchar : (1 : GF n) + 1 = 0 := by
    norm_num
    erw [CharP.cast_eq_zero_iff (GaloisField 2 n) 2]
  have hdouble (z : GF n) : z + z = 0 := by
    calc
      z + z = z * (1 + 1) := by ring
      _ = 0 := by rw [hchar, mul_zero]
  induction k with
  | zero => simpa using (hdouble x).symm
  | succ k ih =>
      rw [Finset.sum_range_succ, ih, add_pow_char_pow]
      have hpow : (x ^ 2) ^ (2 ^ k) = x ^ (2 ^ (k + 1)) := by
        rw [← pow_mul, pow_succ]
        congr 1
        omega
      rw [hpow]
      calc
        x + x ^ (2 ^ k) + (x ^ (2 ^ k) + x ^ (2 ^ (k + 1))) =
            x + (x ^ (2 ^ k) + x ^ (2 ^ k)) + x ^ (2 ^ (k + 1)) := by ring
        _ = x + x ^ (2 ^ (k + 1)) := by rw [hdouble, add_zero]

lemma kasami_normalizedDerivative_mul_quadratic_pow
    (n k : ℕ) (x : GF n) :
    kasamiNormalizedDerivative n k x * (x + x ^ 2) ^ (2 ^ k) =
      (x + x ^ (2 ^ k)) ^ (2 ^ k + 1) := by
  haveI := Fact.mk (show Nat.Prime 2 by decide)
  have hchar : (1 : GF n) + 1 = 0 := by
    norm_num
    erw [CharP.cast_eq_zero_iff (GaloisField 2 n) 2]
  have htwo : (2 : GF n) = 0 := by
    erw [CharP.cast_eq_zero_iff (GaloisField 2 n) 2]
  have hfour : 4 ^ k = 2 ^ (2 * k) := by
    norm_num [show 4 = 2 ^ 2 by norm_num, pow_mul]
  have hle : 2 ^ k ≤ 4 ^ k := by
    rw [hfour]
    exact pow_le_pow_right₀ (by omega) (by omega)
  have hexponent : kasamiExponent k + 2 ^ k = 2 ^ (2 * k) + 1 := by
    unfold kasamiExponent
    rw [hfour]
    omega
  have hfactor : x + x ^ 2 = x * (x + 1) := by ring
  have hshift (r : ℕ) : (x + 1) ^ (2 ^ r) = x ^ (2 ^ r) + 1 := by
    rw [add_pow_char_pow]
    simp
  unfold kasamiNormalizedDerivative kasamiFunction
  rw [hfactor, mul_pow]
  have hx : x ^ kasamiExponent k * x ^ (2 ^ k) = x ^ (2 ^ (2 * k) + 1) := by
    rw [← pow_add, hexponent]
  have hy : (x + 1) ^ kasamiExponent k * (x + 1) ^ (2 ^ k) =
      (x + 1) ^ (2 ^ (2 * k) + 1) := by
    rw [← pow_add, hexponent]
  calc
    (x ^ kasamiExponent k + (x + 1) ^ kasamiExponent k + 1) *
        (x ^ (2 ^ k) * (x + 1) ^ (2 ^ k)) =
        (x ^ kasamiExponent k * x ^ (2 ^ k)) * (x + 1) ^ (2 ^ k) +
          ((x + 1) ^ kasamiExponent k * (x + 1) ^ (2 ^ k)) * x ^ (2 ^ k) +
          x ^ (2 ^ k) * (x + 1) ^ (2 ^ k) := by ring
    _ = x ^ (2 ^ (2 * k) + 1) * (x + 1) ^ (2 ^ k) +
          (x + 1) ^ (2 ^ (2 * k) + 1) * x ^ (2 ^ k) +
          x ^ (2 ^ k) * (x + 1) ^ (2 ^ k) := by rw [hx, hy]
  have hshiftSucc (r : ℕ) : (x + 1) ^ (2 ^ r + 1) =
      (x ^ (2 ^ r) + 1) * (x + 1) := by
    rw [pow_succ', hshift]
    ring
  have hnumerator : (x + x ^ (2 ^ k)) ^ (2 ^ k + 1) =
      (x + x ^ (2 ^ k)) ^ (2 ^ k) * (x + x ^ (2 ^ k)) := by
    rw [pow_succ']
    ring
  rw [hshift k, hshiftSucc (2 * k), hnumerator]
  rw [add_pow_char_pow]
  ring_nf
  rw [htwo]
  ring

/-- The normalized Kasami derivative is the MCM polynomial evaluated at
`x + x^2`. -/
lemma kasamiNormalizedDerivative_eq_genMCMeval
    (n k : ℕ) (hn : 0 < n) (hkn : k < n) (x : GF n) :
    kasamiNormalizedDerivative n k x = genMCMeval n k 0 (x + x ^ 2) := by
  have hchar : (1 : GF n) + 1 = 0 := by
    norm_num
    erw [CharP.cast_eq_zero_iff (GaloisField 2 n) 2]
  have hdpos : 0 < kasamiExponent k := by
    unfold kasamiExponent
    omega
  have hfactor : x + x ^ 2 = x * (x + 1) := by ring
  by_cases hz : x + x ^ 2 = 0
  · have hsplit : x = 0 ∨ x + 1 = 0 := by
      apply eq_zero_or_eq_zero_of_mul_eq_zero
      rw [← hfactor]
      exact hz
    rcases hsplit with hx | hx
    · subst x
      simpa [kasamiNormalizedDerivative, kasamiFunction, genMCMeval_formula,
        psi_beta, hchar, hdpos.ne'] using hchar
    · have hxone : x = 1 := by
        calc
          x = x + 1 + 1 := by rw [add_assoc, hchar, add_zero]
          _ = 1 := by rw [hx, zero_add]
      subst x
      simpa [kasamiNormalizedDerivative, kasamiFunction, genMCMeval_formula,
        psi_beta, hchar, hdpos.ne'] using hchar
  · rw [genMCMeval_eq_div n k 0 (x + x ^ 2) hn hkn hz]
    have hpsi : psi_beta n k 0 (x + x ^ 2) = x + x ^ (2 ^ k) := by
      unfold psi_beta
      simp [mcm_sum_at_quadratic]
    rw [hpsi]
    apply (eq_div_iff (pow_ne_zero _ hz)).2
    exact kasami_normalizedDerivative_mul_quadratic_pow n k x

lemma quadratic_collision
    (n : ℕ) (x y : GF n) (hxy : x + x ^ 2 = y + y ^ 2) :
    y = x ∨ y = x + 1 := by
  have hchar : (1 : GF n) + 1 = 0 := by
    norm_num
    erw [CharP.cast_eq_zero_iff (GaloisField 2 n) 2]
  have htwo : (2 : GF n) = 0 := by
    erw [CharP.cast_eq_zero_iff (GaloisField 2 n) 2]
  have hdouble (z : GF n) : z + z = 0 := by
    calc
      z + z = z * (1 + 1) := by ring
      _ = 0 := by rw [hchar, mul_zero]
  have heq (u v : GF n) (huv : u + v = 0) : u = v := by
    calc
      u = u + 0 := by rw [add_zero]
      _ = u + (u + v) := by rw [huv]
      _ = (u + u) + v := by rw [add_assoc]
      _ = v := by rw [hdouble, zero_add]
  have hzero : (y + x) * (y + x + 1) = 0 := by
    calc
      (y + x) * (y + x + 1) = (y + y ^ 2) + (x + x ^ 2) := by
        ring_nf
        rw [htwo]
        ring
      _ = 0 := by rw [← hxy, hdouble]
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hzero with h | h
  · exact Or.inl (heq y x (by simpa [add_comm] using h))
  · right
    apply heq y (x + 1)
    simpa [add_assoc] using h

/-- The map `x ↦ x + x^2` has fibers of cardinality at most two. -/
lemma quadratic_isTwoToOne (n : ℕ) :
    IsTwoToOne n (fun x : GF n => x + x ^ 2) := by
  classical
  letI := Fintype.ofFinite (GF n)
  unfold IsTwoToOne
  intro b
  let s : Finset (GF n) := Finset.univ.filter fun x => x + x ^ 2 = b
  change s.card ≤ 2
  by_cases hs : s.Nonempty
  · obtain ⟨x, hx⟩ := hs
    have hsubset : s ⊆ {x, x + 1} := by
      intro y hy
      have hx' : x + x ^ 2 = b := by simpa [s] using hx
      have hy' : y + y ^ 2 = b := by simpa [s] using hy
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact quadratic_collision n x y (hx'.trans hy'.symm)
    calc
      s.card ≤ ({x, x + 1} : Finset (GF n)).card := Finset.card_le_card hsubset
      _ ≤ 2 := Finset.card_le_two
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [hempty]
    norm_num

/-- For odd `k`, the Kasami monomial is APN over `GF(2^n)`. -/
theorem kasamiFunction_isAPN_of_odd
    (n k : ℕ)
    (hn : 0 < n) (hk : 0 < k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hkOdd : k % 2 = 1) :
    IsAPN n (kasamiFunction n k) := by
  classical
  letI := Fintype.ofFinite (GF n)
  have hMCM : Function.Bijective (genMCMeval n k 0) := by
    exact mcm_isPermutation n k hn hk hkn hcop hkOdd
  have hfunction : kasamiNormalizedDerivative n k =
      fun x => genMCMeval n k 0 (x + x ^ 2) := by
    funext x
    exact kasamiNormalizedDerivative_eq_genMCMeval n k hn hkn x
  apply (kasamiFunction_isAPN_iff_normalizedDerivative_twoToOne n k).mpr
  rw [hfunction]
  unfold IsTwoToOne
  intro b
  obtain ⟨c, hc⟩ := hMCM.2 b
  have hfilter :
      Finset.univ.filter (fun x => genMCMeval n k 0 (x + x ^ 2) = b) =
        Finset.univ.filter (fun x => x + x ^ 2 = c) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hc]
    exact hMCM.1.eq_iff
  rw [hfilter]
  exact quadratic_isTwoToOne n c

/-- For even `k`, coprimality makes `n-k` odd, so complementary-parameter
transfer reduces APN to the odd case. -/
theorem kasamiFunction_isAPN_of_even
    (n k : ℕ)
    (hn : 0 < n) (hk : 0 < k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hkEven : k % 2 = 0) :
    IsAPN n (kasamiFunction n k) := by
  have hnOdd : n % 2 = 1 := by
    by_contra hnOdd
    have hnEven : n % 2 = 0 := by
      have := Nat.mod_lt n (by omega : 0 < 2)
      omega
    have hkDvd : 2 ∣ k := Nat.dvd_of_mod_eq_zero hkEven
    have hnDvd : 2 ∣ n := Nat.dvd_of_mod_eq_zero hnEven
    have hDvd : 2 ∣ Nat.gcd k n := Nat.dvd_gcd hkDvd hnDvd
    rw [hcop] at hDvd
    norm_num at hDvd
  have hcompOdd : (n - k) % 2 = 1 := by
    omega
  have hcompPos : 0 < n - k := by omega
  have hcompLt : n - k < n := by omega
  have hcompCoprime : Nat.Coprime (n - k) n :=
    (Nat.coprime_self_sub_left (Nat.le_of_lt hkn)).mpr hcop
  have hcompAPN : IsAPN n (kasamiFunction n (n - k)) :=
    kasamiFunction_isAPN_of_odd n (n - k) hn hcompPos hcompLt hcompCoprime hcompOdd
  exact (kasamiFunction_isAPN_iff_complement n k hn hkn).mpr hcompAPN

/-- The Kasami monomial is APN whenever its parameter is positive, smaller
than the extension degree, and coprime to it. -/
theorem kasamiFunction_isAPN
    (n k : ℕ)
    (hn : 0 < n) (hk : 0 < k) (hkn : k < n)
    (hcop : Nat.Coprime k n) :
    IsAPN n (kasamiFunction n k) := by
  by_cases hkEven : k % 2 = 0
  · exact kasamiFunction_isAPN_of_even n k hn hk hkn hcop hkEven
  · have hmodLt : k % 2 < 2 := Nat.mod_lt _ (by omega)
    have hkOdd : k % 2 = 1 := by omega
    exact kasamiFunction_isAPN_of_odd n k hn hk hkn hcop hkOdd

end GeneralizedKasami
