import RequestProject.Walsh.Divisibility

/-!
# The Kasami function is Almost Bent

The main theorem `kasami_is_ab`: for `n` odd and `gcd(k,n)=1`, the Kasami power
function `x ↦ x^{4^k-2^k+1}` on `GF(2^n)` is Almost Bent.

The proof combines three inputs through the abstract moment criterion
`ab_from_moments`:

* the Parseval identity (the Kasami map is a permutation);
* the fourth-moment identity (from the APN property, proved elsewhere in the
  project);
* the `2^{(n+1)/2}`-divisibility of every Walsh coefficient.
-/

open scoped BigOperators
open Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace GeneralizedKasami

/-- **The Kasami function is Almost Bent.**  For `n` odd, `k ≥ 1`, `k < n` and
`gcd(k,n) = 1`, the Kasami power map `x ↦ x^{4^k-2^k+1}` on `GF(2^n)` is AB. -/
theorem kasami_is_ab (n k : ℕ) (hn : 0 < n) (hodd : Odd n) (hk : 0 < k) (hkn : k < n)
    (hcop : Nat.Coprime k n) :
    IsAB n (kasami n k) := by
  have hbij : Function.Bijective (kasami n k) := kasami_bijective n k hn hodd
  have hapn : IsAPN (kasami n k) := kasami_isAPN n k hn hk hkn hcop
  apply ab_from_moments n hn hodd (kasami n k)
  · -- Parseval identity
    intro a _
    exact walsh_parseval n hn (kasami n k) hbij a
  · -- fourth-moment identity
    intro a ha
    exact walsh_fourth_moment_monomial n (kasamiExponent k) hn hbij hapn a ha
  · -- divisibility
    intro a _ b
    exact kasami_walsh_div n k hn hodd a b

end GeneralizedKasami
