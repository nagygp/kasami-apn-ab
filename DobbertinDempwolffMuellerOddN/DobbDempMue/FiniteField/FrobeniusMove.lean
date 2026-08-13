import Mathlib
import DobbDempMue.FiniteField.KasamiDefs
import DobbDempMue.FiniteField.FrobAlg

/-!
# Frobenius Move for Kasami Exponents

Step 1 for the even-`k` reduction:

For
`d(t) = 2^(2t) - 2^t + 1`,
show
`d(n-k) * 2^(2k) = d(k) + (2^n - 1) * (2^n + 1 - 2^k)`.

Over `GF(2^n)`, this yields
`x^(d(k)) = (x^(d(n-k)))^(2^(2k))`.
-/

namespace KasamiAPN

/--
Arithmetic identity behind the Frobenius move from `k` to `n-k`.
-/
lemma kasamiExp_complement_mul_pow (n k : ℕ) (hkn : k ≤ n) :
    kasamiExp (n - k) * 2 ^ (2 * k) =
      kasamiExp k + (2 ^ n - 1) * (2 ^ n + 1 - 2 ^ k) := by
  unfold kasamiExp
  have h2kn : 2 ^ k ≤ 2 ^ n := pow_le_pow_right₀ (by decide) hkn
  have h2nnk : 2 ^ (n - k) ≤ 2 ^ (2 * (n - k)) := by
    exact pow_le_pow_right₀ (by decide) (by omega)
  have h2k2k : 2 ^ k ≤ 2 ^ (2 * k) := by
    exact pow_le_pow_right₀ (by decide) (by omega)
  have h1n : 1 ≤ 2 ^ n := one_le_pow₀ (by decide)
  have h2kn' : 2 ^ k ≤ 2 ^ n + 1 := le_trans h2kn (Nat.le_add_right _ _)
  zify [Nat.cast_sub h2nnk, Nat.cast_sub h2k2k, Nat.cast_sub h1n, Nat.cast_sub h2kn,
    Nat.cast_sub h2kn']
  ring_nf
  have hA : (2 : Int) ^ ((n - k) * 2) * (2 : Int) ^ (k * 2) = (2 : Int) ^ (n * 2) := by
    calc
      (2 : Int) ^ ((n - k) * 2) * (2 : Int) ^ (k * 2)
          = (2 : Int) ^ ((n - k) * 2 + (k * 2)) := by rw [← Int.pow_add]
      _ = (2 : Int) ^ (n * 2) := by
            congr 1
            omega
  have hB : (2 : Int) ^ (n - k) * (2 : Int) ^ (k * 2) = (2 : Int) ^ k * (2 : Int) ^ n := by
    calc
      (2 : Int) ^ (n - k) * (2 : Int) ^ (k * 2)
          = (2 : Int) ^ ((n - k) + (k * 2)) := by rw [← Int.pow_add]
      _ = (2 : Int) ^ (n + k) := by
            congr 1
            omega
      _ = (2 : Int) ^ n * (2 : Int) ^ k := by rw [Int.pow_add]
      _ = (2 : Int) ^ k * (2 : Int) ^ n := by ring
  simp [hA, hB, add_comm, add_left_comm, add_assoc]

/--
Consequently, over `GF(2^n)`, the `k`-Kasami monomial is a Frobenius power of
its `(n-k)` counterpart.
-/
lemma kasami_pow_eq_frob_of_complement
    {F : Type*} [Field F] [Fintype F]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    (k : ℕ) (hkn : k ≤ n) (x : F) :
    x ^ kasamiExp k = (x ^ kasamiExp (n - k)) ^ (2 ^ (2 * k)) := by
  by_cases hx : x = 0
  · subst hx
    simp [kasamiExp]
  · have hFermat : x ^ (2 ^ n - 1) = 1 := by
      simpa [hn] using FiniteField.pow_card_sub_one_eq_one x hx
    have hCardMul : x ^ ((2 ^ n - 1) * (2 ^ n + 1 - 2 ^ k)) = 1 := by
      rw [pow_mul, hFermat, one_pow]
    calc
      x ^ kasamiExp k
        = x ^ kasamiExp k * x ^ ((2 ^ n - 1) * (2 ^ n + 1 - 2 ^ k)) := by
            simp [hCardMul]
      _ = x ^ (kasamiExp k + (2 ^ n - 1) * (2 ^ n + 1 - 2 ^ k)) := by
            rw [pow_add, pow_mul]
      _ = x ^ (kasamiExp (n - k) * 2 ^ (2 * k)) := by
            rw [kasamiExp_complement_mul_pow n k hkn]
      _ = (x ^ kasamiExp (n - k)) ^ (2 ^ (2 * k)) := by
            rw [pow_mul]

/--
APN is invariant under post-composition by Frobenius powers in characteristic 2.
-/
lemma isAPN_frob_pow_iff
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (f : F → F) (r : ℕ) :
    IsAPN f ↔ IsAPN (fun x : F => (f x) ^ (2 ^ r)) := by
  have hfrob_inj : Function.Injective (fun t : F => t ^ (2 ^ r)) := by
    simpa using (DempwolffMueller.frob_bijective (F := F) (p := 2) r).1
  constructor
  · intro hf a ha x y h
    have hpow : (f (x + a) + f x) ^ (2 ^ r) = (f (y + a) + f y) ^ (2 ^ r) := by
      simpa [add_pow_char_pow (p := 2) (n := r)] using h
    exact hf a ha x y (hfrob_inj hpow)
  · intro hf a ha x y h
    have hpow : (f (x + a)) ^ (2 ^ r) + (f x) ^ (2 ^ r) =
        (f (y + a)) ^ (2 ^ r) + (f y) ^ (2 ^ r) := by
      rw [← add_pow_char_pow (p := 2) (n := r), ← add_pow_char_pow (p := 2) (n := r)]
      exact congrArg (fun t : F => t ^ (2 ^ r)) h
    exact hf a ha x y hpow

/--
Step 2 (Frobenius move): over `GF(2^n)`, APN for `d(k)` is equivalent to APN for `d(n-k)`.
-/
lemma kasami_apn_iff_complement
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    (k : ℕ) (hkn : k ≤ n) :
    IsAPN (fun x : F => x ^ kasamiExp k) ↔
    IsAPN (fun x : F => x ^ kasamiExp (n - k)) := by
  have hEq : (fun x : F => x ^ kasamiExp k) =
      (fun x : F => (x ^ kasamiExp (n - k)) ^ (2 ^ (2 * k))) := by
    funext x
    exact kasami_pow_eq_frob_of_complement hn k hkn x
  have hFrob := isAPN_frob_pow_iff (F := F) (fun x : F => x ^ kasamiExp (n - k)) (2 * k)
  constructor
  · intro hk_apn
    have hpow_apn : IsAPN (fun x : F => (x ^ kasamiExp (n - k)) ^ (2 ^ (2 * k))) := by
      simpa [hEq] using hk_apn
    exact hFrob.mpr hpow_apn
  · intro hnk_apn
    have hpow_apn : IsAPN (fun x : F => (x ^ kasamiExp (n - k)) ^ (2 ^ (2 * k))) :=
      hFrob.mp hnk_apn
    simpa [hEq] using hpow_apn

end KasamiAPN
