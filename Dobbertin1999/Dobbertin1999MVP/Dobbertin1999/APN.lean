import Mathlib
import Dobbertin1999MVP.Core.KasamiAPN
import Dobbertin1999MVP.Dobbertin1999.MCMtoAPN

/-!
# Dobbertin (1999) — Corollary 2: Kasami power functions are APN

This module is the **APN** part of the transcription of Dobbertin (1999),
*"Kasami Power Functions, Permutation Polynomials and Cyclic Difference Sets"*.
It records **Corollary 2** of the paper — *Kasami power functions are almost
perfect nonlinear* — as the terminal node of the MCM → APN chain.  Everything is
proved by *reusing* the project's Kasami development; nothing is left as `sorry`.

## Corollary 2 (Dobbertin 1999)

> **Corollary 2.** *Kasami power functions are almost perfect nonlinear.*
>
> *Proof.* If `k' = 1/k (mod n)` is odd, define `q = q₀`, otherwise `q = q₁`.
> According to Theorem 1, `q` is a permutation polynomial.  A routine computation
> shows that `p(t) = 1/q(t^{2^k} + t)`.  On the other hand `t ↦ t^{2^k} + t`
> maps two-to-one, since `gcd(k, n) = 1`. ∎

The paper uses Nyberg's definition of APN: `x ↦ x^d` is **APN** iff for all
`a ∈ L*` and `b ∈ L`, the equation `(x + a)^d + x^d = b` has *either no or
precisely two solutions* in `L`.

## Contents

* `IsAPN` — the collision form of APN (Nyberg's definition, `x^d(x+a)+x^d = …`
  forces `y ∈ {x, x+a}`); re-exported from `KasamiAPN.IsAPN`.
* `kasami_is_apn` — Corollary 2, collision form, via the MCM → APN chain.
* `kasami_is_apn_solution_count` — Corollary 2 in the literal Nyberg phrasing:
  every nonzero derivative equation has `0` or exactly `2` solutions.
-/

namespace Dobbertin1999.APN

open Dobbertin1999.MCMtoAPN

/-- **APN, collision form (Nyberg's definition).**  A map `f` is APN iff for every
nonzero `a`, a derivative collision `f(x+a)+f(x) = f(y+a)+f(y)` forces
`y ∈ {x, x+a}`.  Re-exported from `KasamiAPN.IsAPN`. -/
abbrev IsAPN {F : Type*} [Field F] [CharP F 2] (f : F → F) : Prop :=
  KasamiAPN.IsAPN f

/-- **Corollary 2 (Dobbertin 1999) — Kasami power functions are APN.**

Let `F = 𝔽_{2ⁿ}` with `n` odd, and let `k` be odd with `1 < k < n` and
`gcd(k, n) = 1`.  Then the Kasami power function `x ↦ x^d`, with the Kasami
exponent `d = 2^{2k} − 2^k + 1`, is almost perfect nonlinear.

This is the endpoint of the MCM → APN chain: the Müller–Cohen–Matthews
permutation theorem (`Dobbertin1999.MCM`) enters through the key identity and the
Gold permutation (`Dobbertin1999.MCMtoAPN`) and collapses, via the two-to-one map
`t ↦ t^{2^k} + t`, to the APN property.  Reuses `KasamiAPN.kasami_is_apn`. -/
theorem kasami_is_apn {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (k : ℕ)
    (hk : 1 < k) (hk_odd : Odd k) (hkn : k < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime k n) :
    IsAPN (fun (x : F) => x ^ (kasamiExp k)) :=
  KasamiAPN.kasami_is_apn hn k hk hk_odd hkn hn_odd hcop

/-
**Corollary 2 — literal Nyberg phrasing (solution count).**

For every nonzero `a` and every `b`, the derivative equation
`(x + a)^d + x^d = b` has *either no or precisely two* solutions `x ∈ 𝔽_{2ⁿ}`.
This is Dobbertin's stated form of the APN property.

The count is even because `x ↦ x + a` is a fixed-point-free involution on the
solution set (`a ≠ 0`); together with the collision form `kasami_is_apn`
(which bounds the set by two) the cardinality is `0` or `2`.
-/
theorem kasami_is_apn_solution_count {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (k : ℕ)
    (hk : 1 < k) (hk_odd : Odd k) (hkn : k < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime k n)
    (a : F) (ha : a ≠ 0) (b : F) :
    Nat.card {x : F // (x + a) ^ (kasamiExp k) + x ^ (kasamiExp k) = b} = 0 ∨
    Nat.card {x : F // (x + a) ^ (kasamiExp k) + x ^ (kasamiExp k) = b} = 2 := by
  -- By the APN property, if there are two distinct solutions $x$ and $y$, then $y = x + a$.
  have h_apn : ∀ x y : F, (x + a) ^ (kasamiExp k) + x ^ (kasamiExp k) = b → (y + a) ^ (kasamiExp k) + y ^ (kasamiExp k) = b → y = x ∨ y = x + a := by
    intro x y hx hy;
    apply (kasami_is_apn hn k hk hk_odd hkn hn_odd hcop) a ha x y;
    grind;
  by_cases h : ∃ x : F, ( x + a ) ^kasamiExp k + x ^kasamiExp k = b <;> simp_all +decide [ Nat.card_eq_zero ];
  obtain ⟨ x, hx ⟩ := h;
  refine' Or.inr _;
  rw [ show { x : F // ( x + a ) ^ kasamiExp k + x ^ kasamiExp k = b } = { x : F | ( x + a ) ^ kasamiExp k + x ^ kasamiExp k = b } from rfl, show { x : F | ( x + a ) ^ kasamiExp k + x ^ kasamiExp k = b } = { x, x + a } from ?_ ];
  · simp +decide [ ha ];
  · grind +splitImp

end Dobbertin1999.APN