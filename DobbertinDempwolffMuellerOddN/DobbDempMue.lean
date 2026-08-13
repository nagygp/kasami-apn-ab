import DobbDempMue.DempwolffMueller2013.MCM
import DobbDempMue.Dobbertin1999.MCMtoAPN
import DobbDempMue.Dobbertin1999.APN
import DobbDempMue.AlmostBent.KasamiAB

/-!
# Dobbertin (1999) — MCM, MCM → APN, APN: standalone MVP entry point

This is the single entry point for a **standalone, minimal, end-to-end**
formalisation of the **MCM**, **MCM → APN**, and **APN** parts of

> Hans Dobbertin, *"Kasami Power Functions, Permutation Polynomials and Cyclic
> Difference Sets"*, in *Difference Sets, Sequences and their Correlation
> Properties*, NATO Sci. Ser. C **542**, Kluwer Academic Publishers, 1999,
> pp. 133–158.

This folder (`DobbDempMue/`) is a self-contained extract of the larger
`RequestProject` development: it contains **only** the modules that actually
contribute to the three headline transcriptions below, plus their finite-field
prerequisites.  Every statement is proved end to end; the whole chain is
`sorry`-free and rests only on the standard axioms `propext`, `Classical.choice`,
`Quot.sound`.

The APN result formalised here is **only for odd extension degree** `n`: throughout
the final Kasami theorem, `F = 𝔽_{2ⁿ}` and `Odd n`. The exponent parameter `k`
need not itself be odd.

## Module layout

* `DobbDempMue/FiniteField/` — the finite-field engine: exponent arithmetic
  (`ExpArith`), Frobenius algebra (`FrobAlg`), trace/norm (`TraceNorm`), the
  additive-adjoint bijection (`AdjointBij`), the Lemma 3.1 skeleton
  (`BareLemma31Skeleton`), and the Müller–Cohen–Matthews permutation theorem
  `DempwolffMueller.theorem_3_2` (`Thm32`).
* `DobbDempMue/DempwolffMueller2013/KasamiAPN.lean` — the Kasami APN engine built on top of
  the MCM permutation theorem (key identity, Gold permutation, injectivity
  bridge, two-to-one collapse, `KasamiAPN.kasami_is_apn_odd_n`).
* `DobbDempMue/Dobbertin1999/` — the paper transcription in three parts:
    * `MCM.lean` — the MCM permutation polynomial theorem (Section 2);
    * `MCMtoAPN.lean` — the bridge used in the proof of Corollary 2;
    * `APN.lean` — Corollary 2: Kasami power functions are APN.

## The MCM → APN chain, end to end

This chain concludes the APN theorem only when `n` is odd. For odd `k`, the MCM
argument below applies directly. For even `k`, the proof uses the Frobenius move
`KasamiAPN.kasami_apn_iff_complement` to replace `k` with `n - k`; since `n` is
odd, `n - k` is odd, so the direct odd-`k` argument applies to the complementary
Kasami exponent. The exceptional complementary parameter `n - k = 1` is the
cubic (`x ↦ x³`) case.

```
DempwolffMueller.MCM.mcm_permutation_ktransfer        (Müller–Cohen–Matthews / Theorem 1 engine)
        │   x ↦ L_k(x)·x^{k'} is a permutation of 𝔽_{2ⁿ}
        ▼
Dobbertin1999.MCMtoAPN.kasami_key_identity          ((x+1)^d + x^d + 1)·(x²+x)^{2^k} = (x^{2^k}+x)^{2^k+1}
Dobbertin1999.MCMtoAPN.gold_permutation             y ↦ y^{2^k+1} bijective
Dobbertin1999.MCMtoAPN.mcm_injective_bridge         MCM ∘ Gold injectivity
Dobbertin1999.MCMtoAPN.kasami_collision_forces_equal_u   collision ⟹ x²+x = y²+y
        │   (t ↦ t^{2^k}+t is two-to-one)
        ▼
KasamiAPN.kasami_apn_iff_complement                 even k: Frobenius move k ↦ n-k
        ▼                                            (n-k is odd when n is odd)
Dobbertin1999.APN.kasami_is_apn                     Corollary 2, odd n: x ↦ x^d is APN
Dobbertin1999.APN.kasami_is_apn_solution_count      Nyberg form: 0 or exactly 2 solutions
```
-/

namespace Dobbertin1999.Headlines

/-- **MCM permutation theorem** (Müller–Cohen–Matthews). See
`Dobbertin1999.MCM.mcm_permutation`. -/
alias mcm_permutation := DempwolffMueller.MCM.mcm_permutation

/-- **Dempwolff–Mueller permutation theorem, `k'`-transfer form** — the shape consumed by the
APN chain.  See `DempwolffMueller.MCM.dempwolff_mueller_permutation_ktransfer`. -/
alias mcm_permutation_ktransfer := DempwolffMueller.MCM.dempwolff_mueller_permutation_ktransfer

/-- **The key identity** linking the Kasami derivative to the Gold exponent.  See
`Dobbertin1999.MCMtoAPN.kasami_key_identity`. -/
alias kasami_key_identity := Dobbertin1999.MCMtoAPN.kasami_key_identity

/-- **Corollary 2** — Kasami power functions are APN (collision form).  See
`Dobbertin1999.APN.kasami_is_apn`. -/
alias kasami_is_apn := Dobbertin1999.APN.kasami_is_apn

/-- **Corollary 2** — Kasami power functions are APN (Nyberg solution-count form).
See `Dobbertin1999.APN.kasami_is_apn_solution_count`. -/
alias kasami_is_apn_solution_count := Dobbertin1999.APN.kasami_is_apn_solution_count

/-- **APN -> AB** — Almost Bent property follows from APN plus quadratic trick
when `n` is odd. See `AlmostBent.KasamiAB.kasami_is_ab`. -/
alias kasami_is_ab := KasamiAB.kasami_is_ab

end Dobbertin1999.Headlines
