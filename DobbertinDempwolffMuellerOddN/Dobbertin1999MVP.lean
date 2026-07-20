import Dobbertin1999MVP.Dobbertin1999.MCM
import Dobbertin1999MVP.Dobbertin1999.MCMtoAPN
import Dobbertin1999MVP.Dobbertin1999.APN

/-!
# Dobbertin (1999) — MCM, MCM → APN, APN: standalone MVP entry point

This is the single entry point for a **standalone, minimal, end-to-end**
formalisation of the **MCM**, **MCM → APN**, and **APN** parts of

> Hans Dobbertin, *"Kasami Power Functions, Permutation Polynomials and Cyclic
> Difference Sets"*, in *Difference Sets, Sequences and their Correlation
> Properties*, NATO Sci. Ser. C **542**, Kluwer Academic Publishers, 1999,
> pp. 133–158.

This folder (`Dobbertin1999MVP/`) is a self-contained extract of the larger
`RequestProject` development: it contains **only** the modules that actually
contribute to the three headline transcriptions below, plus their finite-field
prerequisites.  Every statement is proved end to end; the whole chain is
`sorry`-free and rests only on the standard axioms `propext`, `Classical.choice`,
`Quot.sound`.

## Module layout

* `Dobbertin1999MVP/FiniteField/` — the finite-field engine: exponent arithmetic
  (`ExpArith`), Frobenius algebra (`FrobAlg`), trace/norm (`TraceNorm`), the
  additive-adjoint bijection (`AdjointBij`), the Lemma 3.1 skeleton
  (`BareLemma31Skeleton`), and the Müller–Cohen–Matthews permutation theorem
  `DempwolffMueller.theorem_3_2` (`Thm32`).
* `Dobbertin1999MVP/Core/KasamiAPN.lean` — the Kasami APN engine built on top of
  the MCM permutation theorem (key identity, Gold permutation, injectivity
  bridge, two-to-one collapse, `KasamiAPN.kasami_is_apn`).
* `Dobbertin1999MVP/Dobbertin1999/` — the paper transcription in three parts:
    * `MCM.lean` — the MCM permutation polynomial theorem (Section 2);
    * `MCMtoAPN.lean` — the bridge used in the proof of Corollary 2;
    * `APN.lean` — Corollary 2: Kasami power functions are APN.

## The MCM → APN chain, end to end

```
Dobbertin1999.MCM.mcm_permutation_ktransfer        (Müller–Cohen–Matthews / Theorem 1 engine)
        │   x ↦ L_k(x)·x^{k'} is a permutation of 𝔽_{2ⁿ}
        ▼
Dobbertin1999.MCMtoAPN.kasami_key_identity          ((x+1)^d + x^d + 1)·(x²+x)^{2^k} = (x^{2^k}+x)^{2^k+1}
Dobbertin1999.MCMtoAPN.gold_permutation             y ↦ y^{2^k+1} bijective
Dobbertin1999.MCMtoAPN.mcm_injective_bridge         MCM ∘ Gold injectivity
Dobbertin1999.MCMtoAPN.kasami_collision_forces_equal_u   collision ⟹ x²+x = y²+y
        │   (t ↦ t^{2^k}+t is two-to-one)
        ▼
Dobbertin1999.APN.kasami_is_apn                     Corollary 2: x ↦ x^d is APN
Dobbertin1999.APN.kasami_is_apn_solution_count      Nyberg form: 0 or exactly 2 solutions
```
-/

namespace Dobbertin1999.Headlines

/-- **MCM permutation theorem** (Müller–Cohen–Matthews). See
`Dobbertin1999.MCM.mcm_permutation`. -/
alias mcm_permutation := Dobbertin1999.MCM.mcm_permutation

/-- **MCM permutation theorem, `k'`-transfer form** — the shape consumed by the
APN chain.  See `Dobbertin1999.MCM.mcm_permutation_ktransfer`. -/
alias mcm_permutation_ktransfer := Dobbertin1999.MCM.mcm_permutation_ktransfer

/-- **The key identity** linking the Kasami derivative to the Gold exponent.  See
`Dobbertin1999.MCMtoAPN.kasami_key_identity`. -/
alias kasami_key_identity := Dobbertin1999.MCMtoAPN.kasami_key_identity

/-- **Corollary 2** — Kasami power functions are APN (collision form).  See
`Dobbertin1999.APN.kasami_is_apn`. -/
alias kasami_is_apn := Dobbertin1999.APN.kasami_is_apn

/-- **Corollary 2** — Kasami power functions are APN (Nyberg solution-count form).
See `Dobbertin1999.APN.kasami_is_apn_solution_count`. -/
alias kasami_is_apn_solution_count := Dobbertin1999.APN.kasami_is_apn_solution_count

end Dobbertin1999.Headlines
