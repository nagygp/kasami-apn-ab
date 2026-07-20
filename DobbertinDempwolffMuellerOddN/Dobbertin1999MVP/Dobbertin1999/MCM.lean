import Mathlib
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
* `mcm_permutation` — the MCM permutation theorem: `x ↦ L_m(x)·x^{e}` is a
  bijection of `𝔽_{2ⁿ}` for the canonical exponent `e = 2^{n-1} − 2^{m-1} − 1`,
  when `1 < m < n`, `m` odd and `gcd(m, n) = 1`.
* `mcm_permutation_ktransfer` — the `k'`-transfer form (`x ↦ L_m(x)·x^{k'}` for
  any exponent `k'` with `(2^{n-1} − 2^{m-1} − 1)·k' ≡ 2^{m-1} (mod 2ⁿ−1)`),
  which is the shape actually consumed by the MCM → APN chain.
-/

namespace Dobbertin1999.MCM

open DempwolffMueller

/-- The **linearized (truncated) trace** `L_m(x) = Σ_{i=0}^{m-1} x^{2^i}`, the
numerator building block of the MCM polynomial `P_β`.  Re-exported from
`DempwolffMueller.truncTrace`. -/
abbrev truncTrace {F : Type*} [CommSemiring F] (m : ℕ) (x : F) : F :=
  DempwolffMueller.truncTrace m x

/-- **The MCM permutation theorem (Dobbertin 1999, Section 2; Müller–Cohen–Matthews).**

Let `F = 𝔽_{2ⁿ}`.  For `m` odd with `1 < m < n` and `gcd(m, n) = 1`, the map
```
   x  ↦  L_m(x) · x^{2^{n-1} − 2^{m-1} − 1}
```
is a permutation of `F`, where `L_m(x) = Σ_{i=0}^{m-1} x^{2^i}`.  This is the
Müller–Cohen–Matthews permutation polynomial `P₀` in the linearized coordinates
used by Dobbertin, and it is the engine that drives the APN proof of Corollary 2.

Proved by reusing `DempwolffMueller.theorem_3_2`. -/
theorem mcm_permutation {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (m : ℕ)
    (hm_pos : 1 < m) (hm_odd : Odd m) (hm_lt : m < n)
    (hcop : Nat.Coprime m n) :
    Function.Bijective (fun x : F =>
      truncTrace m x * x ^ (2 ^ (n - 1) - 2 ^ (m - 1) - 1)) :=
  DempwolffMueller.theorem_3_2 hn m hm_pos hm_odd hm_lt hcop

/-- **The MCM permutation theorem, `k'`-transfer form.**

For any exponent `k'` satisfying the transfer congruence
`(2^{n-1} − 2^{m-1} − 1)·k' ≡ 2^{m-1} (mod 2ⁿ−1)`, the map `x ↦ L_m(x)·x^{k'}`
is still a permutation of `𝔽_{2ⁿ}`.  This is the exact shape that the
MCM → APN chain feeds through (`Dobbertin1999.MCMtoAPN`); it corresponds to the
inverse-exponent packaging `k' ≡ 1/k (mod n)` of the paper.

Proved by reusing `DempwolffMueller.LxXk'_bijective`. -/
theorem mcm_permutation_ktransfer {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (m : ℕ)
    (hm_pos : 1 < m) (hm_odd : Odd m) (hm_lt : m < n)
    (hcop : Nat.Coprime m n) (k' : ℕ)
    (hk' : (2 ^ (n - 1) - 2 ^ (m - 1) - 1) * k' % (2 ^ n - 1) =
            2 ^ (m - 1) % (2 ^ n - 1)) :
    Function.Bijective (fun x : F => truncTrace m x * x ^ k') :=
  DempwolffMueller.LxXk'_bijective hn m hm_pos hm_odd hm_lt hcop k' hk'

end Dobbertin1999.MCM
