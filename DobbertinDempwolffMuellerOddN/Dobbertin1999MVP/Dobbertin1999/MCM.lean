import Mathlib
import Dobbertin1999MVP.Core.KasamiAPN
import Dobbertin1999MVP.FiniteField.Thm32

/-!
# Dobbertin (1999) — the MCM permutation polynomials

This module is the **MCM** part of a faithful, end-to-end transcription of
Hans Dobbertin, *"Kasami Power Functions, Permutation Polynomials and Cyclic
Difference Sets"* (in *Difference Sets, Sequences and their Correlation
Properties*, NATO Sci. Ser. C **542**, Kluwer, 1999, pp. 133–158).

It records the **Müller–Cohen–Matthews (MCM) permutation polynomial** engine that
underlies the paper's route to the APN property of Kasami power functions
(Corollary 2).  Everything here is proved by *reusing* the project's finite-field
development (`Dobbertin1999MVP/FiniteField/Thm32.lean`); nothing is re-proved from
scratch and nothing is left as `sorry`.

## The paper's setup (Section 2)

Throughout, `L = 𝔽_{2ⁿ}`, `Tr : 𝔽_{2ⁿ} → 𝔽₂` is the absolute trace, and one
assumes
```
gcd(k, n) = 1,   k < n,   k' ≡ 1/k (mod n).
```
For `β = 0, 1` the paper defines the **generalized MCM polynomial**
```
                ( Σ_{i=0}^{k-1} z^{2^i}  +  β·Tr(z) )^{2^k + 1}
   P_β(z)  =    ────────────────────────────────────────────────
                                  z^{2^k}
```
(the factor `1/z^{2^k}` being replaced by `z^{(2ⁿ−1) − 2^k}` to obtain a genuine
polynomial on `L`, with the convention `0/0 = 0`).  The paper recalls that `P₀`
is *the* classical **MCM permutation polynomial when `k` is odd**.

Writing `L_k(z) = Σ_{i=0}^{k-1} z^{2^i}` for the truncated (linearized) trace,
`P₀(z) = L_k(z)^{2^k+1} · z^{−2^k}`.  The linearized substitution used in the
paper (Theorem 4) converts `P₀` into the map `x ↦ L_{k'}(x)·x^{k'}` on which the
permutation property is verified; this is exactly the statement carried out in
the project as `DempwolffMueller.theorem_3_2` (Müller–Cohen–Matthews) and its
`k'`-transfer companion `DempwolffMueller.LxXk'_bijective`.

## Contents

* `truncTrace` — the linearized trace `L_m(x) = Σ_{i=0}^{m-1} x^{2^i}`
  (re-exported from the project development).
* `dempwolff_mueller_permutation` — the Dempwolff-Müller permutation theorem:
  `x ↦ L_m(x)·x^{e}` is a
  bijection of `𝔽_{2ⁿ}` for the canonical exponent `e = 2^{n-1} − 2^{m-1} − 1`,
  when `1 < m < n`, `m` odd and `gcd(m, n) = 1`.
* `dempwolff_mueller_permutation_ktransfer` — the `k'`-transfer form
  (`x ↦ L_m(x)·x^{k'}` for any exponent `k'` with
  `(2^{n-1} − 2^{m-1} − 1)·k' ≡ 2^{m-1} (mod 2ⁿ−1)`), which is the shape
  actually consumed by the MCM → APN chain.
-/

namespace Dobbertin1999.MCM

open DempwolffMueller

/-- The **linearized (truncated) trace** `L_m(x) = Σ_{i=0}^{m-1} x^{2^i}`, the
numerator building block of the MCM polynomial `P_β`.  Re-exported from
`DempwolffMueller.truncTrace`. -/
abbrev truncTrace {F : Type*} [CommSemiring F] (m : ℕ) (x : F) : F :=
  DempwolffMueller.truncTrace m x

/-- The **Müller-Cohen-Matthews polynomial** in linearized-trace form:
`MCM_{n,m}(x) = L_m(x)^{2^m + 1} · x^{2^n - 1 - 2^m}`.  On `𝔽_{2^n}`, this
is `L_m(x)^{2^m + 1} / x^{2^m}`, with the polynomial convention at zero. -/
def MCMpol {F : Type*} [CommSemiring F] (n m : ℕ) (x : F) : F :=
  truncTrace m x ^ (2 ^ m + 1) * x ^ (2 ^ n - 1 - 2 ^ m)

/-- Under the Dempwolff-Müller transfer congruence, the MCM polynomial factors
through the Dempwolff-Müller map followed by the `(2^m + 1)`-st power map. -/
theorem MCM_eq_dempwolff_mueller_pow {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (m k' : ℕ)
    (hk'_pos : 0 < k') (x : F) :
    k' * (2 ^ m + 1) % (2 ^ n - 1) =
      (2 ^ n - 1 - 2 ^ m) % (2 ^ n - 1) →
    MCMpol n m x = (truncTrace m x * x ^ k') ^ (2 ^ m + 1) := by
  intro h_exp_mod
  unfold MCMpol
  rw [mul_pow, ← pow_mul]
  by_cases hx : x = 0
  · have h_exp_pos : 0 < k' * (2 ^ m + 1) :=
      Nat.mul_pos hk'_pos (by positivity)
    rw [hx, show truncTrace m (0 : F) = 0 from DempwolffMueller.truncTrace_zero m]
    simp [h_exp_pos.ne']
  · conv_lhs => rw [← Nat.mod_add_div (2 ^ n - 1 - 2 ^ m) (2 ^ n - 1)]
    conv_rhs => rw [← Nat.mod_add_div (k' * (2 ^ m + 1)) (2 ^ n - 1)]
    rw [← h_exp_mod]
    simp [pow_add, pow_mul, ← hn, FiniteField.pow_card_sub_one_eq_one x hx]

/-- **The Dempwolff-Müller permutation theorem (Dempwolff and Müller 2013, Section 3).**

Let `F = 𝔽_{2ⁿ}`.  For `m` odd with `1 < m < n` and `gcd(m, n) = 1`, the map
```
   x  ↦  L_m(x) · x^{2^{n-1} − 2^{m-1} − 1}
```
is a permutation of `F`, where `L_m(x) = Σ_{i=0}^{m-1} x^{2^i}`.  This is the
Dempwolff-Müller permutation polynomial in the linearized coordinates used by
Dobbertin, and it is the engine that drives the APN proof of Corollary 2.

Proved by reusing `DempwolffMueller.theorem_3_2`. -/
theorem dempwolff_mueller_permutation {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (m : ℕ)
    (hm_pos : 1 < m) (hm_odd : Odd m) (hm_lt : m < n)
    (hcop : Nat.Coprime m n) :
    Function.Bijective (fun x : F =>
      truncTrace m x * x ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) :=
  DempwolffMueller.theorem_3_2 hn m hm_pos hm_odd hm_lt hcop

/-- **The Dempwolff-Müller permutation theorem, `k'`-transfer form.**

For any exponent `k'` satisfying the transfer congruence
`(2^{n-1} − 2^{m-1} − 1)·k' ≡ 2^{m-1} (mod 2ⁿ−1)`, the map `x ↦ L_m(x)·x^{k'}`
is still a permutation of `𝔽_{2ⁿ}`.  This is the exact shape that the
MCM → APN chain feeds through (`Dobbertin1999.MCMtoAPN`); it corresponds to the
inverse-exponent packaging `k' ≡ 1/k (mod n)` of the paper.

Proved by reusing `DempwolffMueller.LxXk'_bijective`. -/
theorem dempwolff_mueller_permutation_ktransfer {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (m : ℕ)
    (hm_pos : 1 < m) (hm_odd : Odd m) (hm_lt : m < n)
    (hcop : Nat.Coprime m n) (k' : ℕ)
    (hk' : (2 ^ (n - 1) - 2 ^ (m - 1) - 1) * k' % (2 ^ n - 1) =
            2 ^ (m - 1) % (2 ^ n - 1)) :
    Function.Bijective (fun x : F => truncTrace m x * x ^ k') :=
  DempwolffMueller.LxXk'_bijective hn m hm_pos hm_odd hm_lt hcop k' hk'


/-- **The Müller-Cohen-Matthews permutation theorem (Dempwolff and Müller 2013).**

**The Gold permutation.**

`y ↦ y^{2^k + 1}` is a bijection of `𝔽_{2ⁿ}` when `0 < k`, `n` is odd and
`gcd(k, n) = 1` (equivalently `gcd(2^k + 1, 2ⁿ − 1) = 1`).  This is the second
factor of the MCM ∘ Gold composite.  Reuses `KasamiAPN.gold_pow_bijective`. -/

lemma gold_permutation {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : 0 < k) (hn_pos : 0 < n)
    (hcop : Nat.Coprime k n) (hn_odd : Odd n) :
    Function.Bijective (fun y : F => y ^ (2 ^ k + 1)) :=
  KasamiAPN.gold_pow_bijective hn k hk hn_pos hcop hn_odd

/-- **The Müller-Cohen-Matthews permutation theorem.**

For odd `m < n` with `gcd(m, n) = 1`, the MCM polynomial
`x ↦ L_m(x)^{2^m + 1} / x^{2^m}` permutes `𝔽_{2^n}`.  The proof factors it as
the Gold power map after a Dempwolff-Müller permutation. -/
theorem mcm_permutation {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (m : ℕ)
    (hm_pos : 0 < m) (hm_odd : Odd m) (hm_lt : m < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime m n) :
    Function.Bijective (MCMpol n m : F → F) := by
  by_cases hm_one : m = 1
  · subst m
    have h_exp_le : 2 ^ 1 + 1 ≤ 2 ^ n := by
      have h_four_le : 2 ^ 2 ≤ 2 ^ n :=
        pow_le_pow_right₀ (by decide) (by omega)
      norm_num at h_four_le ⊢
      omega
    have h_mcm : (MCMpol n 1 : F → F) = id := by
      funext x
      have h_trace : truncTrace (F := F) 1 x = x := by
        simp [DempwolffMueller.truncTrace]
      rw [MCMpol, h_trace]
      norm_num
      rw [← pow_add]
      have h_exp : 3 + (2 ^ n - 1 - 2) = 2 ^ n := by omega
      rw [h_exp, ← hn, FiniteField.pow_card]
    rw [h_mcm]
    exact Function.bijective_id
  have hm_gt : 1 < m := by omega
  obtain ⟨k', h_factor, h_transfer⟩ :=
    KasamiAPN.exists_linking_exp hm_gt (by omega) hm_lt hcop hn_odd
  have h_pow_succ_le : 2 ^ (m + 1) ≤ 2 ^ n :=
    pow_le_pow_right₀ (by decide) (by omega)
  have hm_nonzero : m ≠ 0 := by omega
  have h_pow_gt_one : 1 < 2 ^ m :=
    one_lt_pow₀ one_lt_two hm_nonzero
  have h_pow_lt : 2 ^ m < 2 ^ n - 1 := by
    rw [pow_succ] at h_pow_succ_le
    omega
  have h_factor_pos : 0 < 2 ^ n - 1 - 2 ^ m := by
    exact Nat.sub_pos_of_lt h_pow_lt
  have h_factor_lt : 2 ^ n - 1 - 2 ^ m < 2 ^ n - 1 :=
    Nat.sub_lt (Nat.sub_pos_of_lt (by
      exact one_lt_pow₀ one_lt_two (by omega))) (by positivity)
  have hk'_pos : 0 < k' := by
    by_contra hk'_pos
    have hk'_zero : k' = 0 := Nat.eq_zero_of_not_pos hk'_pos
    rw [hk'_zero] at h_factor
    simp [Nat.mod_eq_of_lt h_factor_lt] at h_factor
    omega
  have h_transfer' :
      k' * (2 ^ (n - 1) - 1 - 2 ^ (m - 1)) % (2 ^ n - 1) =
        2 ^ (m - 1) % (2 ^ n - 1) := by
    have h_pred_lt : m - 1 < n - 1 := by omega
    have hpow : 2 ^ (m - 1) < 2 ^ (n - 1) :=
      pow_lt_pow_right₀ (by decide) h_pred_lt
    rw [show 2 ^ (n - 1) - 1 - 2 ^ (m - 1) =
      2 ^ (n - 1) - 2 ^ (m - 1) - 1 by omega, Nat.mul_comm]
    exact h_transfer
  have h_dempwolff : Function.Bijective (fun x : F => truncTrace m x * x ^ k') :=
    dempwolff_mueller_permutation_ktransfer hn m hm_gt hm_odd hm_lt hcop k' h_transfer
  have h_gold : Function.Bijective (fun y : F => y ^ (2 ^ m + 1)) :=
    gold_permutation hn m (by omega) (by omega) hcop hn_odd
  have h_factorization : ∀ x : F,
      MCMpol n m x = (truncTrace m x * x ^ k') ^ (2 ^ m + 1) :=
    fun x => MCM_eq_dempwolff_mueller_pow hn m k' hk'_pos x h_factor
  rw [show (MCMpol n m : F → F) = (fun y : F => y ^ (2 ^ m + 1)) ∘
      (fun x : F => truncTrace m x * x ^ k') by
    funext x
    simp only [Function.comp_apply]
    exact h_factorization x]
  exact h_gold.comp h_dempwolff


end Dobbertin1999.MCM
