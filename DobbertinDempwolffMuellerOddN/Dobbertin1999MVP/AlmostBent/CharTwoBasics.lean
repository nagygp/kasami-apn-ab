import Dobbertin1999MVP.AlmostBent.Defs

/-!
# Characteristic 2 Basics and Linearized Polynomial Lemmas

Foundational lemmas for characteristic 2 fields needed by the collision analysis.

## Key results
- Char-2 arithmetic: `char2_add_self`, `char2_neg`, `char2_sub`
- Frobenius additivity: `freshman_sq`, `freshman_pow`
- Linearized polynomial `L_k`: additivity, kernel triviality
- `sVal` pairing: `sVal(t) = sVal(t+1)`
- Cross form: additivity, factorization, kernel characterization
-/

set_option maxHeartbeats 800000

namespace CollisionAnalysis

open Finset Fintype

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-! ## Characteristic 2 arithmetic -/

omit [Fintype F] [DecidableEq F] in
theorem char2_add_self (x : F) : x + x = 0 := CharTwo.add_self_eq_zero x

omit [Fintype F] [DecidableEq F] in
theorem char2_neg (x : F) : -x = x := CharTwo.neg_eq x

omit [Fintype F] [DecidableEq F] in
theorem char2_sub (x y : F) : x - y = x + y := CharTwo.sub_eq_add x y

omit [Fintype F] [DecidableEq F] in
/-- `(x+y)² = x² + y²` in characteristic 2. -/
theorem freshman_sq (x y : F) : (x + y) ^ 2 = x ^ 2 + y ^ 2 :=
  add_pow_char_of_commute 2 (Commute.all x y)

omit [Fintype F] [DecidableEq F] in
/-- `(x+y)^{2^k} = x^{2^k} + y^{2^k}` — the Frobenius map is additive. -/
theorem freshman_pow (x y : F) (k : ℕ) :
    (x + y) ^ (2 ^ k) = x ^ (2 ^ k) + y ^ (2 ^ k) :=
  add_pow_char_pow_of_commute 2 k (Commute.all x y)

/-! ## Linearized polynomial L_k -/

/-- `L` is additive: `L(x+y) = L(x) + L(y)`. -/
theorem L_add (k : ℕ) (x y : F) : L k (x + y) = L k x + L k y := by
  simp [L, freshman_pow]; ring

omit [Fintype F] [DecidableEq F] in
theorem L_zero (k : ℕ) : L k (0 : F) = 0 := by simp [L]

omit [Fintype F] [DecidableEq F] in
theorem L_one (k : ℕ) : L k (1 : F) = 0 := by
  simp [L, one_pow, CharTwo.add_self_eq_zero]

/-! ## sVal pairing -/

omit [Fintype F] [DecidableEq F] in
/-- `sVal(t) = sVal(t+1)` — differential values come in pairs. -/
theorem sVal_pairing (k : ℕ) (t : F) : sVal k t = sVal k (t + 1) := by
  simp only [sVal]
  have : t + 1 + 1 = t := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [this]; ring

/-! ## Cross form -/

/-- Cross form is additive in the second argument. -/
theorem cross_add (k : ℕ) (s P₁ P₂ : F) :
    Cross k s (P₁ + P₂) = Cross k s P₁ + Cross k s P₂ := by
  simp only [Cross, freshman_pow, mul_add]; ring

omit [Fintype F] [DecidableEq F] [CharP F 2] in
/-- Cross-norm factorization: `Cross(s, P) = N(s) · L(P/s)` when `s ≠ 0`. -/
theorem cross_eq_norm_L (k : ℕ) (s P : F) (hs : s ≠ 0) :
    Cross k s P = N k s * L k (P / s) := by
  simp only [Cross, N, L]; rw [div_pow, mul_add]
  congr 1 <;> (field_simp; ring)

omit [Fintype F] [DecidableEq F] [CharP F 2] in
/-- Cross form vanishes iff `L(P/s) = 0` when `s ≠ 0`. -/
theorem cross_zero_iff (k : ℕ) (s P : F) (hs : s ≠ 0) :
    Cross k s P = 0 ↔ L k (P / s) = 0 := by
  rw [cross_eq_norm_L k s P hs]; constructor
  · intro h; exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hs)
  · intro h; rw [h, mul_zero]

/-! ## Kernel of L_k -/

/-- When `gcd(k,n) = 1`, `L_k(x) = 0` implies `x ∈ {0, 1}`. -/
theorem L_ker_trivial {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (hcop : Nat.Coprime k n) (x : F) (hx : L k x = 0) :
    x = 0 ∨ x = 1 := by
  by_cases hx0 : x = 0 <;> simp_all +decide [L]
  have hx_pow : x ^ (2 ^ k - 1) = 1 := by
    cases m : 2 ^ k <;> simp_all +decide [pow_succ, add_eq_zero_iff_eq_neg]
    grobner
  have hx_gcd : x ^ Nat.gcd (2 ^ k - 1) (2 ^ n - 1) = 1 := by
    rw [Nat.gcd_comm, pow_gcd_eq_one]
    exact ⟨by rw [← hcard, FiniteField.pow_card_sub_one_eq_one x hx0], hx_pow⟩
  simp_all +decide [Nat.Coprime, Nat.Coprime.gcd_eq_one]

/-! ## Cross form triviality -/

/-- When `gcd(k,n) = 1` and `s ≠ 0`, `Cross(s, P) = 0 ↔ P ∈ {0, s}`. -/
theorem cross_zero_iff_trivial {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (hcop : Nat.Coprime k n) (s P : F) (hs : s ≠ 0) :
    Cross k s P = 0 ↔ (P = 0 ∨ P = s) := by
  rw [cross_zero_iff k s P hs]
  constructor
  · intro h
    rcases L_ker_trivial hcard k hcop _ h with h0 | h1
    · left; exact (div_eq_zero_iff.mp h0).resolve_right hs
    · right; rwa [div_eq_one_iff_eq hs] at h1
  · rintro (rfl | rfl)
    · simp [L]
    · rw [div_self hs]; exact L_one k

end CollisionAnalysis
