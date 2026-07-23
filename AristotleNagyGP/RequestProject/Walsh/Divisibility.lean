import RequestProject.Walsh.Fourth

/-!
# Divisibility of the Kasami Walsh coefficients

Every Walsh coefficient of the Kasami function `x ↦ x^{4^k-2^k+1}` on `GF(2^n)`
with `n` odd and `gcd(k,n)=1` is divisible by `2^{(n+1)/2}`.

The argument substitutes `x = y^{2^k+1}` (a permutation of the field, since
`gcd(2^k+1, 2^n-1) = 1`), which rewrites the Walsh sum as the character sum of a
quadratic function `Q(y) = a·y^{2^k+1} + b·y^{2^{3k}+1}`.  The square of a
quadratic character sum is divisible by `2^n`; since `n` is odd, this upgrades to
`2^{(n+1)/2}` dividing the sum itself.
-/

open scoped BigOperators
open Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace GeneralizedKasami

/-- The gold exponent identity `(2^k+1)·(4^k-2^k+1) = 2^{3k}+1`. -/
lemma gold_kasami_exp (k : ℕ) :
    (2 ^ k + 1) * kasamiExponent k = 2 ^ (3 * k) + 1 := by
  unfold kasamiExponent
  have h1 : (2 : ℕ) ^ k ≤ 4 ^ k := Nat.pow_le_pow_left (by norm_num) k
  zify [h1]
  have e4 : (4 : ℤ) ^ k = 2 ^ k * 2 ^ k := by
    rw [show (4:ℤ) = 2 * 2 by norm_num, mul_pow]
  have e3 : (2 : ℤ) ^ (3 * k) = 2 ^ k * 2 ^ k * 2 ^ k := by
    rw [← pow_add, ← pow_add]; congr 1; ring
  rw [e4, e3]; ring

/-- `gcd(2^a+1, 2^n-1) = 1` whenever `n` is odd. -/
lemma gold_coprime (n a : ℕ) (hodd : Odd n) :
    Nat.Coprime (2 ^ a + 1) (2 ^ n - 1) := by
  rw [Nat.Coprime, Nat.gcd_comm]
  apply Nat.Coprime.symm
  rw [Nat.coprime_comm]
  apply Nat.coprime_of_dvd
  intro k hk hkd1 hkd2
  -- k is prime, k ∣ 2^n - 1, k ∣ 2^a + 1
  -- First, k ≠ 2 since 2^a + 1 is odd
  have hk_ne_2 : k ≠ 2 := by
    intro heq
    rw [heq] at hkd1
    have hodd2 : Odd (2 ^ n - 1) := by
      have hn_pos : 0 < n := Nat.pos_of_ne_zero (fun h => by simp [h] at hodd)
      have heven : Even (2 ^ n) := even_iff_two_dvd.mpr (dvd_pow_self 2 hn_pos.ne')
      rw [Nat.odd_iff]
      have hdvd : 2 ∣ 2 ^ n := dvd_pow_self 2 hn_pos.ne'
      rw [Nat.dvd_iff_mod_eq_zero] at hdvd
      rw [← Nat.mod_add_div (2^n) 2, hdvd]
      have hm : 1 ≤ 2 ^ n / 2 := by
        have : 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn_pos
        omega
      omega
    exact hodd2.not_two_dvd_nat hkd1
  -- Use ZMod for modular arithmetic
  have hn_pos : 0 < n := Nat.pos_of_ne_zero (fun h => by simp [h] at hodd)
  have hka : (2 : ZMod k) ^ a = -1 := by
    have h := hkd2
    have h' : (k : ℤ) ∣ (2 ^ a + 1 : ℤ) := by exact_mod_cast h
    have h'' : ((2 ^ a + 1 : ℤ) : ZMod k) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact h'
    simp only [Int.cast_add, Int.cast_pow, Int.cast_ofNat, Int.cast_one] at h''
    exact eq_neg_of_add_eq_zero_left h''
  -- From hkd1: k ∣ 2^n - 1, we get 2^n = 1 in ZMod k
  have hkn : (2 : ZMod k) ^ n = 1 := by
    have h := hkd1
    have h' : (k : ℤ) ∣ (2 ^ n - 1 : ℤ) := by
      have hn1 : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
      have := h
      rw [← Int.natCast_dvd_natCast] at this
      simp [Int.natCast_sub hn1] at this
      exact this
    have h'' : ((2 ^ n - 1 : ℤ) : ZMod k) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact h'
    simp only [Int.cast_sub, Int.cast_pow, Int.cast_ofNat, Int.cast_one] at h''
    exact sub_eq_zero.mp h''
  -- 2^{2a} = 1 since (2^a)^2 = (-1)^2 = 1
  have hka2 : (2 : ZMod k) ^ (2 * a) = 1 := by
    rw [mul_comm, pow_mul, hka]
    norm_num
  -- 2^{gcd(2a, n)} = 1
  have hgcd : (2 : ZMod k) ^ Nat.gcd (2 * a) n = 1 := pow_gcd_eq_one.mpr ⟨hka2, hkn⟩
  -- Since n is odd, gcd(2*a, n) = gcd(a, n) | a
  have hcoprime : Nat.Coprime 2 n := by
    rcases hodd with ⟨m, rfl⟩
    norm_num [Nat.coprime_mul_iff_right]
  have hgcd_eq : Nat.gcd (2 * a) n = Nat.gcd a n := by
    rw [Nat.gcd_comm, Nat.gcd_comm a]
    exact hcoprime.gcd_mul_left_cancel_right a
  have hgcd_div_a : Nat.gcd (2 * a) n ∣ a := by
    rw [hgcd_eq]
    exact Nat.gcd_dvd_left a n
  -- So 2^a = 1 in ZMod k
  have hka1 : (2 : ZMod k) ^ a = 1 := by
    obtain ⟨m, hm⟩ := hgcd_div_a
    rw [hm, pow_mul, hgcd, one_pow]
  -- But 2^a = -1, so 1 = -1, meaning 2 = 0 in ZMod k
  have h2_eq_0 : (2 : ZMod k) = 0 := by
    have : (1 : ZMod k) = -1 := hka1.symm.trans hka
    have := add_eq_zero_iff_eq_neg.mpr this
    convert this using 1
    norm_num
  -- So k | 2
  have hk2 : k ∣ 2 := by
    have h := h2_eq_0
    rw [show (2 : ZMod k) = (2 : ℕ) by norm_cast] at h
    have : (2 : ℤ) = (0 : ZMod k) := by simpa using h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    exact_mod_cast this
  -- k is prime and k | 2, so k = 2, contradicting hk_ne_2
  have := Nat.dvd_prime Nat.prime_two |>.mp hk2
  rcases this with rfl | rfl
  · exact Nat.not_prime_one hk
  · exact hk_ne_2 rfl

/-- **The Gold map is a permutation.**  `y ↦ y^{2^a+1}` is a bijection of `GF(2^n)`
whenever `n` is odd. -/
lemma gold_bijective (n a : ℕ) (hn : 0 < n) (hodd : Odd n) :
    Function.Bijective (fun y : GF n => y ^ (2 ^ a + 1)) := by
  have hcop := gold_coprime n a hodd
  -- Handle n = 1 separately (GF(2) has only 2 elements, map is identity on {0,1})
  by_cases hn1 : n = 1
  · subst hn1
    have hcard : Fintype.card (GF 1) = 2 := by
      rw [← Nat.card_eq_fintype_card]; exact GaloisField.card 2 1 (by norm_num)
    have h : ∀ x : GF 1, x ^ (2 ^ a + 1) = x := by
      intro x
      by_cases hx : x = 0
      · simp [hx]
      · have h2 : x ^ Fintype.card (GF 1) = x := FiniteField.pow_card x
        rw [hcard] at h2
        simp_all [pow_succ]
    simp [h]
  -- For n ≥ 2, use coprimality
  have hn2 : 2 ≤ n := by omega
  have hgt : 1 < 2 ^ n - 1 := by
    have : 2 ^ n ≥ 4 := Nat.le_trans (by norm_num : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) hn2)
    omega
  obtain ⟨m, _, hm⟩ : ∃ m < 2 ^ n - 1, (2 ^ a + 1) * m % (2 ^ n - 1) = 1 :=
    Nat.exists_mul_mod_eq_one_of_coprime hcop hgt
  -- Show that y ↦ y^m is the inverse
  have hinv : ∀ x : GF n, x ^ ((2 ^ a + 1) * m) = x := by
    intro x
    rw [← Nat.mod_add_div ((2 ^ a + 1) * m) (2 ^ n - 1), hm]
    have hcard : Nat.card (GF n) = 2 ^ n := GaloisField.card 2 n hn.ne'
    by_cases hx : x = 0
    · simp [hx]
    · have hx_pow : x ^ (2 ^ n - 1) = 1 := by
        have : Fintype.card (GF n) = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hcard]
        convert FiniteField.pow_card_sub_one_eq_one x hx using 1
        rw [this]
      simp_all [pow_add, pow_mul]
  -- Construct the equivalence using x ↦ x^(2^a+1) and x ↦ x^m as inverses
  have hinv2 : ∀ x : GF n, x ^ (m * (2 ^ a + 1)) = x := by simpa [mul_comm] using hinv
  refine ⟨?_, ?_⟩
  · -- Injective: if x^(2^a+1) = y^(2^a+1), then x = y
    intro x y hxy
    simp only at hxy
    have : x ^ (m * (2 ^ a + 1)) = y ^ (m * (2 ^ a + 1)) := by
      have h1 : x ^ (m * (2 ^ a + 1)) = (x ^ (2 ^ a + 1)) ^ m := by rw [mul_comm, pow_mul]
      have h2 : y ^ (m * (2 ^ a + 1)) = (y ^ (2 ^ a + 1)) ^ m := by rw [mul_comm, pow_mul]
      rw [h1, h2, hxy]
    rw [hinv2 x, hinv2 y] at this
    exact this
  · -- Surjective: for any x, there exists y with y^(2^a+1) = x
    intro x
    use x ^ m
    simp only
    rw [← pow_mul, hinv2]

/-- The Kasami monomial is a permutation of `GF(2^n)` when `n` is odd. -/
lemma kasami_bijective (n k : ℕ) (hn : 0 < n) (hodd : Odd n) :
    Function.Bijective (kasami n k) := by
  have hg := gold_bijective n k hn hodd
  have hh := gold_bijective n (3 * k) hn hodd
  have hcomp : (kasami n k) ∘ (fun y : GF n => y ^ (2 ^ k + 1))
      = (fun y : GF n => y ^ (2 ^ (3 * k) + 1)) := by
    funext y
    simp only [Function.comp_apply, kasami]
    rw [← pow_mul, gold_kasami_exp k]
  have hcompbij : Function.Bijective ((kasami n k) ∘ (fun y : GF n => y ^ (2 ^ k + 1))) := by
    rw [hcomp]; exact hh
  exact (Function.Bijective.of_comp_iff _ hg).mp hcompbij

/-- Rewriting the Kasami Walsh sum after the Gold substitution. -/
lemma walsh_kasami_eq_gold (n k : ℕ) (hn : 0 < n) (hodd : Odd n)
    (a b : GF n) :
    walsh n (kasami n k) a b =
      ∑ y : GF n, signChar n (a * y ^ (2 ^ k + 1) + b * y ^ (2 ^ (3 * k) + 1)) := by
  unfold walsh kasami
  rw [← Equiv.sum_comp (Equiv.ofBijective _ (gold_bijective n k hn hodd))]
  apply Finset.sum_congr rfl
  intro y _
  simp only [Equiv.ofBijective_apply]
  congr 2
  rw [← pow_mul, gold_kasami_exp k]

/-- **Additive character sums are divisible by `2^n`.**  If `ℓ : GF(2^n) → GF(2^n)`
is additive, then `∑_y χ(ℓ y)` is divisible by `2^n`. -/
lemma sum_signChar_additive_dvd (n : ℕ) (hn : 0 < n) (ℓ : GF n → GF n)
    (hadd : ∀ y z : GF n, ℓ (y + z) = ℓ y + ℓ z) :
    (2 ^ n : ℤ) ∣ (∑ y : GF n, signChar n (ℓ y)) := by
  by_cases hall : ∀ y : GF n, signChar n (ℓ y) = 1
  · -- sum is 2^n
    have : (∑ y : GF n, signChar n (ℓ y)) = 2 ^ n := by
      rw [Finset.sum_congr rfl (fun y _ => hall y)]
      rw [Finset.sum_const, Finset.card_univ, card_GF n hn]; simp
    rw [this]
  · -- exists y0 with χ = -1; translation gives sum = 0
    push_neg at hall
    obtain ⟨y0, hy0⟩ := hall
    have hy0' : signChar n (ℓ y0) = -1 := by
      unfold signChar at hy0 ⊢; split at hy0 <;> simp_all
    have hreindex : (∑ y : GF n, signChar n (ℓ (y + y0))) = ∑ y : GF n, signChar n (ℓ y) :=
      Equiv.sum_comp (Equiv.addRight y0) (fun y => signChar n (ℓ y))
    have hstep : (∑ y : GF n, signChar n (ℓ (y + y0)))
        = - (∑ y : GF n, signChar n (ℓ y)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro y _
      rw [hadd, signChar_add n hn, hy0']; ring
    rw [hreindex] at hstep
    have : (∑ y : GF n, signChar n (ℓ y)) = 0 := by linarith
    rw [this]; exact dvd_zero _
  
/-- The Gold-quadratic function `Q(y) = a·y^{2^k+1} + b·y^{2^{3k}+1}`. -/
noncomputable def Qgold (n k : ℕ) (a b y : GF n) : GF n :=
  a * y ^ (2 ^ k + 1) + b * y ^ (2 ^ (3 * k) + 1)

/-- The associated bilinear form `B(u,y) = Q(y)+Q(y+u)+Q(u)+Q(0)`. -/
noncomputable def goldB (n k : ℕ) (a b u y : GF n) : GF n :=
  Qgold n k a b y + Qgold n k a b (y + u) + Qgold n k a b u + Qgold n k a b 0

/-- For the Gold-quadratic, `B(u, ·)` is additive in its second argument. -/
lemma goldB_additive (n k : ℕ) (a b u : GF n) :
    ∀ y z : GF n, goldB n k a b u (y + z) = goldB n k a b u y + goldB n k a b u z := by
  intro y z
  unfold goldB Qgold
  haveI : ExpChar (GF n) 2 := inferInstance
  -- Frobenius: (x + y) ^ 2^m = x ^ 2^m + y ^ 2^m
  have frob : ∀ m : ℕ, ∀ x y : GF n, (x + y) ^ 2 ^ m = x ^ 2 ^ m + y ^ 2 ^ m := fun m x y => add_pow_char_pow x y 2 m
  -- Rewrite 8^k as 2^(3*k)
  have h8k : (8 : ℕ) ^ k = 2 ^ (3 * k) := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
  -- Apply pow_add to split exponents
  simp_rw [pow_add]
  -- Expand all Frobenius terms
  have expand_frob : ∀ x y : GF n, ∀ m : ℕ, (x + y) ^ 2 ^ m = x ^ 2 ^ m + y ^ 2 ^ m := fun x y m => frob m x y
  simp only [expand_frob]
  ring_nf
  have h2 : (2 : GF n) = 0 := by rw [show (2 : GF n) = 1 + 1 by norm_num, CharTwo.add_self_eq_zero]
  have h4 : (4 : GF n) = 0 := by rw [show (4 : GF n) = 2 + 2 by norm_num, h2]; simp
  simp [h2, h4]

/-- Expansion of the square of the quadratic character sum. -/
lemma gold_sum_sq_eq (n k : ℕ) (hn : 0 < n) (a b : GF n) :
    (∑ y : GF n, signChar n (Qgold n k a b y)) ^ 2
      = ∑ u : GF n, signChar n (Qgold n k a b u + Qgold n k a b 0)
          * (∑ y : GF n, signChar n (goldB n k a b u y)) := by
  -- Expand to double sum
  rw [sq, Finset.sum_mul]
  have h1 : ∀ i, signChar n (Qgold n k a b i) * ∑ y, signChar n (Qgold n k a b y) =
      ∑ y, signChar n (Qgold n k a b i + Qgold n k a b y) := by
    intro i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [signChar_add n hn]
  simp_rw [h1]
  -- Reindex: for each x, substitute u = x + y, so y = x + u
  have h2 : ∀ x, ∑ y, signChar n (Qgold n k a b x + Qgold n k a b y) =
      ∑ u, signChar n (Qgold n k a b x + Qgold n k a b (x + u)) := by
    intro x
    rw [← Equiv.sum_comp (Equiv.addLeft x)]
    rfl
  simp_rw [h2]
  -- Swap order of summation: outer should be over shift variable u
  rw [Finset.sum_comm]
  -- Use the goldB relation: Q(y) + Q(y+u) = goldB n k a b u y + Q(u) + Q(0)
  have h3 : ∀ u y, Qgold n k a b y + Qgold n k a b (y + u) = goldB n k a b u y + (Qgold n k a b u + Qgold n k a b 0) := by
    intro x u
    unfold goldB Qgold
    abel_nf
    simp [two_mul]
    simp [CharTwo.add_self_eq_zero]
  simp_rw [h3]
  -- Split signChar of sum into product
  have h4 : ∀ y u, signChar n (goldB n k a b u y + (Qgold n k a b u + Qgold n k a b 0)) =
      signChar n (Qgold n k a b u + Qgold n k a b 0) * signChar n (goldB n k a b u y) := by
    intro y u
    rw [signChar_add n hn]
    ring
  simp_rw [h4, Finset.mul_sum]

/-- **Quadratic character sum square divisibility.**  For the Gold-quadratic
`Q(y) = a·y^{2^k+1} + b·y^{2^{3k}+1}`, the square of `∑_y χ(Q y)` is divisible by
`2^n`. -/
lemma gold_quad_sq_dvd (n k : ℕ) (hn : 0 < n) (a b : GF n) :
    (2 ^ n : ℤ) ∣ (∑ y : GF n, signChar n (a * y ^ (2 ^ k + 1) + b * y ^ (2 ^ (3 * k) + 1))) ^ 2 := by
  have hrw : (∑ y : GF n, signChar n (a * y ^ (2 ^ k + 1) + b * y ^ (2 ^ (3 * k) + 1)))
      = ∑ y : GF n, signChar n (Qgold n k a b y) := rfl
  rw [hrw, gold_sum_sq_eq n k hn a b]
  apply Finset.dvd_sum
  intro u _
  exact Dvd.dvd.mul_left
    (sum_signChar_additive_dvd n hn (goldB n k a b u) (goldB_additive n k a b u)) _

/-- **2-adic upgrade.**  If `2^n ∣ S^2` and `n` is odd, then `2^{(n+1)/2} ∣ S`. -/
lemma two_adic_upgrade (n : ℕ) (hodd : Odd n) (S : ℤ) (h : (2 : ℤ) ^ n ∣ S ^ 2) :
    (2 : ℤ) ^ ((n + 1) / 2) ∣ S := by
  by_cases hS : S = 0
  · simp [hS]
  · -- The 2-adic valuation of S^2 is at least n
    have hv : n ≤ padicValInt 2 (S ^ 2) := by
      have habs : (2 : ℕ) ^ n ∣ S.natAbs ^ 2 := by
        have : (2 : ℤ) ^ n ∣ S.natAbs ^ 2 := by simpa using h
        exact_mod_cast this
      have hv1 : n ≤ padicValNat 2 (S.natAbs ^ 2) := by
        have h2 : Nat.Prime 2 := Nat.prime_two
        have := h2.pow_dvd_iff_le_factorization (by simp [hS]) |>.mp habs
        simp [Nat.factorization_pow] at this
        rw [padicValNat.pow 2 (by simp [hS] : S.natAbs ≠ 0)]
        exact this
      convert hv1 using 1
      simp [padicValInt, Int.natAbs_pow]
    -- Now use hv to show 2^((n+1)/2) ∣ S
    -- padicValInt 2 (S^2) = 2 * padicValInt 2 S
    have hv2 : n ≤ 2 * padicValInt 2 S := by
      have : padicValInt 2 (S ^ 2) = 2 * padicValInt 2 S := by
        simp only [pow_two]
        rw [padicValInt.mul hS hS]
        ring
      rw [this] at hv
      exact hv
    -- Since n is odd, n = 2m + 1, so 2m + 1 ≤ 2 * v_2(S), meaning v_2(S) ≥ m + 1 = (n+1)/2
    have hodd' : ∃ m, n = 2 * m + 1 := hodd
    obtain ⟨m, hm⟩ := hodd'
    have hdiv : padicValInt 2 S ≥ (n + 1) / 2 := by
      simp [hm]
      omega
    -- Use Int.coe_natAbs to convert
    have h2S : (2 : ℤ) ^ ((n + 1) / 2) ∣ S := by
      have hnat : padicValNat 2 S.natAbs ≥ (n + 1) / 2 := by
        have : padicValInt 2 S = padicValNat 2 S.natAbs := rfl
        linarith
      have hdvd_nat : (2 : ℕ) ^ ((n + 1) / 2) ∣ S.natAbs := by
        have hne : S.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hS
        rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne]
        exact hnat
      rw [← Int.natAbs_dvd_natAbs]
      exact_mod_cast hdvd_nat
    exact h2S

/-- **Kasami Walsh divisibility.**  Every Walsh coefficient of the Kasami function
is divisible by `2^{(n+1)/2}`. -/
theorem kasami_walsh_div (n k : ℕ) (hn : 0 < n) (hodd : Odd n)
    (a b : GF n) :
    (2 : ℤ) ^ ((n + 1) / 2) ∣ walsh n (kasami n k) a b := by
  rw [walsh_kasami_eq_gold n k hn hodd]
  apply two_adic_upgrade n hodd
  exact gold_quad_sq_dvd n k hn a b

end GeneralizedKasami
