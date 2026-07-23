# Summary of changes for run 3c8867ed-c662-476e-bb01-f31d2c5bf57c
I formalized and fully proved that the Kasami power function x ↦ x^(4^k − 2^k + 1) on GF(2^n) is **Almost Bent (AB)** when n is odd, k ≥ 1, k < n, and gcd(k,n) = 1, following the approach in the attached paper (kasami-is-AB.pdf).

The development builds with no `sorry`/`admit` and no added axioms; the main theorem `GeneralizedKasami.kasami_is_ab` depends only on the standard axioms `propext`, `Classical.choice`, `Quot.sound`.

New files (under `RequestProject/Walsh/`) and what they prove:

- `Character.lean` — the absolute trace `Tr(z) = Σ_{i<n} z^{2^i}`, the sign character χ(z) = (−1)^{Tr z}, its additivity/multiplicativity, and the fundamental orthogonality relation `Σ_x χ(c·x) = 2^n` if c = 0 else 0.
- `AB.lean` — the Walsh transform `W_f(a,b) = Σ_x χ(a·x + b·f(x))`, the Almost Bent predicate `IsAB`, and the abstract moment criterion `ab_from_moments`: a permutation whose Walsh spectrum satisfies Parseval, the fourth-moment identity, and 2^{(n+1)/2}-divisibility is AB (via an integer-lattice argument reducing Σ(k^4 − k^2) = 0 to k^2 ∈ {0,1}).
- `Parseval.lean` — the Parseval identity `Σ_b W_f(a,b)^2 = 2^{2n}` for a permutation f.
- `Fourth.lean` — the fourth-moment identity `Σ_b W_f(a,b)^4 = 2·2^{3n}` for a permutation APN monomial and nonzero a. This is obtained by reducing the moment to a weighted quadruple count, evaluating the total count (2^{3n}, from bijectivity) and the "linear-structure" count (3·2^{2n} − 2·2^n, from the APN 2-to-1 property), and combining them via a scaling/character reindexing identity.
- `Divisibility.lean` — 2^{(n+1)/2} divides every Kasami Walsh coefficient. Uses the Gold substitution x = y^{2^k+1} (a permutation, since gcd(2^k+1, 2^n−1) = 1 for n odd), the exponent identity (2^k+1)(4^k−2^k+1) = 2^{3k}+1 that turns the Walsh sum into a quadratic character sum, divisibility of the square of a quadratic character sum by 2^n (via additivity of the associated bilinear form), and a 2-adic upgrade valid for odd n.
- `KasamiAB.lean` — the main theorem `kasami_is_ab`, assembling the three inputs through `ab_from_moments`, using the already-proved APN theorem (`kasami_isAPN`) and permutation property of the Kasami map.

The file `RequestProject.lean` now also imports `RequestProject.KasamiAB`. The previously established results in the project (including the APN theorem) were reused rather than duplicated. The full project builds successfully.

# Summary of changes for run 025a5c88-3508-462b-8a80-aa56005f9ee7
Created `RequestProject/KasamiAPN.lean` and imported it from `RequestProject.lean`.

The new file formalizes and proves:
- the Kasami exponent and monomial evaluation function;
- definitions of two-to-one fibers (`AtMostTwo`) and the APN property;
- the complementary-exponent arithmetic identity and its finite-field consequence;
- invariance of APN under Frobenius postcomposition and replacement of `k` by `n-k`;
- reduction of a monomial’s APN property to its derivative at `1`;
- the identity between the Kasami derivative and the MCM polynomial evaluated at `x+x²`;
- the two-to-one property of `x ↦ x+x²`;
- the APN theorem for odd `k` using `MCMpolynomial_isPermutation`;
- the final theorem `kasami_isAPN` for all positive coprime `k<n`, handling even `k` via the complementary exponent.

The full project builds successfully. The new file contains no `sorry`, `admit`, or unresolved proof suggestions. The principal APN theorem and MCM identity use only the permitted standard axioms (`propext`, `Classical.choice`, and `Quot.sound`). All changes were committed and pushed.

# Summary of changes for run 1474fc34-fa54-4460-a3ea-3e04021722b0
Formalized and proved the MCM permutation-polynomial corollary in `RequestProject/MCMCorollary.lean`.

Added:
- `MCMpolynomial`, matching the stated polynomial
  `z * (∑ i < k, z^(2^i - 1))^(2^k + 1)`;
- the separate field evaluation function `MCMeval`;
- a Bézout/inverse lemma producing suitable `kInv` and `nPrime` from coprimality;
- `MCMeval_eq_genMCMeval_zero`, proving that the MCM polynomial’s evaluation agrees with the generalized MCM evaluation at `β = 0`;
- `MCMpolynomial_isPermutation`, proving that for positive coprime `n,k`, with `k<n` and `k` odd, the MCM polynomial is a permutation polynomial over `GF(2^n)` as a corollary of Dobbertin’s Theorem 4.

Imported the new module from `RequestProject.lean`. The project builds successfully, the new file contains no `sorry`, `admit`, or unresolved proof suggestions, and the principal theorem uses only the permitted standard axioms (`propext`, `Classical.choice`, and `Quot.sound`). All changes were committed and pushed.

# Summary of changes for run a2333e37-8b6d-49c7-871a-00287866653e
Created `RequestProject/genMCM.lean` and added it to the root library import.

The new file includes:
- `genMCMpol`, the generalized MCM polynomial from page 135.
- `genMCMeval`, its separate field evaluation map.
- The transfer maps `psi_beta` and `phi_alpha`.
- The parity-transfer relation from Dobbertin’s Theorem 4.
- A proof that the two transfer maps are mutual inverses and hence bijections.
- Both functional transfer identities:
  - `q_α ∘ ψ_β = inv ∘ P_β`
  - `P_β ∘ φ_α = inv ∘ q_α`
- `dobbertin_theorem4`, proving the one-to-one correspondence between the generalized Kasami and generalized MCM permutation polynomials, including bijectivity of both transfer maps and both polynomial evaluation maps.

The complete project builds successfully. `genMCM.lean` contains no `sorry`, `admit`, or unresolved proof suggestions, and the main theorem uses only the permitted standard axioms (`propext`, `Classical.choice`, and `Quot.sound`). All changes were committed and pushed.

# Summary of changes for run 8a130bfe-4a51-494a-93c0-87c9e0df94a2
Created `Skeleton.md` explaining the proof of `generalizedKasami_isPermutation_iff`. It covers:

- the polynomial/evaluation definitions and fiber equation;
- necessity of the parity condition;
- Frobenius, trace, and linearized-polynomial reductions;
- both cases according to whether `c = γ^(2^k+1) + γ`;
- the auxiliary `Q` and `Delta` arguments;
- uniqueness in the relevant fibers;
- the final passage from injectivity to bijectivity;
- a roadmap connecting each proof stage to the corresponding Lean files and lemmas.

`ARISTOTLE_SUMMARY.md` was read for context and left unchanged.

# Summary of changes for run df9b17b3-b849-4581-a30a-39eaf5626d0d
Completed the requested renaming:

- `RequestProject/Main.lean` → `RequestProject/basic.lean`
- `RequestProject/Final.lean` → `RequestProject/genkasamipol.lean`
- `polynomial` → `genKasamiPol`
- `evaluation` → `genKasamiEval`

Updated all imports and references accordingly, including the root `RequestProject.lean` module. `ARISTOTLE_SUMMARY.md` was not modified.

The full project builds successfully, contains no `sorry` or `admit`, and the main theorems retain only the permitted standard axioms. Changes were committed and pushed.

# Summary of changes for run 19d58b6e-8720-4d01-8cc1-53c763cb9826
Removed the remarks and standalone counterexample lemmas concerning the earlier imprecise instructions. Reworded the remaining documentation to describe only the precise proved statements, while preserving the corrected definitions and theorem proofs. `ARISTOTLE_SUMMARY.md` was left unchanged as requested.

The full project still builds successfully and contains no `sorry` or `admit`.

# Summary of changes for run f7b021a4-be3b-4991-a4f7-921b82c3636c
Completed the requested formalization and the remaining generalized Kasami proof.

- Added `RequestProject/EllSteps.lean` with machine-checked proofs of:
  - **(11)** `ell(x) = Q(x)^(2^k) + (Delta^(2^k-1))⁻¹ * Q(x)`.
  - **(12)** `ell(x)=0 ↔ Q(x)=0 ∨ Q(x)=Delta⁻¹`.
- Completed `kasamiEquation_unique_of_exists_gamma` using the new factorization, the parity contradiction for the `Q(x)=0` case, and `e0_plus_e1_equals_one` for two distinct elements in the `Q(x)=Delta⁻¹` fiber.
- Consequently, the final permutation criterion `generalizedKasami_isPermutation_iff` and its evaluation-function formulation are now fully proved.
- Split the final layer into `RequestProject/Final.lean` and added `RequestProject.lean` as the default library entry point.
- The complete default target builds successfully with no `sorry`, `admit`, or unresolved proof suggestions. The principal theorems use only the permitted standard axioms (`propext`, `Classical.choice`, and `Quot.sound`).
- All changes were committed and pushed.

# Summary of changes for run 2ba80145-9e4a-414e-9587-776e2002d7ad
Added `RequestProject/PairSteps.lean` with machine-checked proofs of all three requested statements:

- `pair_sum_eq_delta`: proves `x₀ + x₁ = Delta` by combining Steps (8) and (9).
- `pair_trace_eq`: proves the absolute traces of `x₀` and `x₁` are equal using the sum identity and Step (10).
- `e0_plus_e1_equals_one`: defines the requested expression through `eTerm` and proves `e₀ + e₁ = 1`.

Also proved the supporting telescoping lemma `iteratedKasamiSum_delta` for the Kasami sum of `Delta`.

The new module builds successfully, contains no `sorry` or `admit`, and all four results use only the permitted standard axioms. Changes were committed and pushed.

# Summary of changes for run 8b4893d1-79b7-4be8-a3d3-68689df227f0
Added `RequestProject/DeltaSteps.lean` with machine-checked formalizations of statements (6)–(10):

- Defined `IsDelta` for the displayed reciprocal equation.
- Proved existence of a nonzero `Delta` using coprimality of `2^k-1` and `2^n-1`.
- Proved `Delta^(2^k) = gamma*Delta + (gamma*Delta)^(2^k)`.
- Proved the requested equivalence between `Q(x)=1/Delta` and the scaled linearized equation.
- Proved that equal values of `x ↦ x^(2^k)+x` imply `x=y` or `x=y+1`.
- Proved that the absolute trace sum of `Delta` is zero.

The existence theorem explicitly records the nonvanishing conditions implicit in the reciprocal notation and the preceding second-case setup: `gamma ≠ 0` and `gamma^(2^k+1)+gamma ≠ 0`.

`RequestProject.DeltaSteps` builds successfully, contains no `sorry` or `admit`, and all five requested results use only standard permitted axioms. The pre-existing unrelated `sorry` in `RequestProject/Main.lean` was left unchanged.

# Summary of changes for run b1539358-1e9c-4022-8edd-7be969dfc4f4
Added `RequestProject/GammaSteps.lean`, defining `c`, the polynomial `Q`, its evaluation formula, and the iterated Kasami sum. All new results are machine-checked and the module builds without `sorry` or `admit`.

The requested statements needed several corrections, which are formalized explicitly:

- **(1)** is true only under `γ ≠ 0`. Without it, `γ=z=0` is a counterexample. The corrected equivalence is proved.
- **(2)** had an index shift. The proved form is
  `z^(2^((i+1)k)) = (γz)^(2^(ik)) + (γz)^(2^((i+1)k)) + 1`,
  obtained by applying the `2^(ik)` Frobenius map to (1).
- **(3)** as stated is false when `n` is odd. The exact result is
  `Tr(z) = n (mod 2)` in the prime subfield. Thus `Tr(z)=0` when `n` is even. A checked counterexample for odd `n` is included (`n=3`, `k=1`, `γ=z=1`).
- **(4)** was missing the constant `kInv mod 2`. The proved telescoping identity is
  `Σ z^(2^(ik)) = γz + (γz)^2 + kInv (mod 2)`.
  Its originally requested form follows when `kInv` is even. A checked counterexample to the unrestricted form is included.
- **(5)** is proved in its exact prime-subfield form:
  `c z^(2^k+1) + Σ z^(2^(ik)) + α Tr(z) = kInv + αn (mod 2)`.
  The omitted constants in (3) and (4) are precisely what produce this right-hand side. This result also needs `γ ≠ 0`; a checked counterexample without that condition is included.

The proofs use Frobenius injectivity and trace invariance, finite-field Frobenius periodicity from `k*kInv ≡ 1 [MOD n]`, and an explicit telescoping sum.

# Summary of changes for run 17924b86-51e7-430c-9bf2-60c2f57312a8
Proved `linearized_unique_of_not_exists_gamma` in `RequestProject/Main.lean` for positive `n`.

Added and proved two supporting lemmas:
- `gf_frobenius_pow_card`: every element of `GF(2^n)` is fixed by the `2^n`-power map.
- `ell_0_eval_factorization`: the requested identity expressing `ell_0(z)` as `c⁻¹ * B² * z`, with `A` and `B` as in the prompt.

The uniqueness proof now derives the forbidden representation of `c` whenever two distinct roots exist, using the factorization and `ell_eval_eq_iff_ell_0_sub_eq_zero`. The relevant theorem has only the standard permitted axioms, and the project builds successfully. The separate, pre-existing sorry in `kasamiEquation_unique_of_exists_gamma` remains unchanged.

# Summary of changes for run 11756328-c29b-4e03-a1aa-c513767fb48c
Updated `RequestProject/Main.lean` with:

- `ell n k c`, the affine linearized polynomial
  `c^(2^k) X^(2^(2k)) + X^(2^k) + cX + 1`.
- `ell_0 n k c := ell n k c + 1`, together with evaluation lemmas for both polynomials.
- A proved lemma `ell_eval_eq_iff_ell_0_sub_eq_zero` stating
  `ell(x) = ell(y) ↔ ell_0(x - y) = 0`.
- Updated statements and usage of `kasamiEquation_implies_linearized` and `linearized_unique_of_not_exists_gamma` to use `ell` notation.

Because the field has characteristic two, `ell_0 = ell + 1` has expanded form
`c^(2^k) X^(2^(2k)) + X^(2^k) + cX`; the two constant `1` terms cancel. This resolves the duplicated `+ 1` in the prompt consistently with the requested identity.

The project builds successfully. The two pre-existing sorries described in `ARISTOTLE_SUMMARY.md` remain unchanged.

# Summary of changes for run 896803c8-e4fd-44bf-88ab-a493e3e648be
Updated `RequestProject/Main.lean` to align the formalization with Dobbertin’s Theorem 1 and its proof structure from the attached paper.

Completed and machine-checked:
- Separate definitions of the generalized Kasami polynomial and its field evaluation function.
- The necessary parity direction.
- Equivalence between polynomial fibers and Dobbertin’s Kasami equation.
- Frobenius periodicity on `GF(2^n)`.
- Frobenius invariance of the absolute trace sum.
- The endpoint-shift identity for the iterated Kasami sum.
- Derivation of Dobbertin’s linearized Equation (2).
- Uniqueness of the zero fiber under the odd-parity condition.
- The final case-split assembly and reduction from fiber uniqueness to bijectivity.

The Lean file builds successfully. Two explicitly marked `sorry`s remain in the substantive case analysis from pages 136–138 of the paper:
- `linearized_unique_of_not_exists_gamma`
- `kasamiEquation_unique_of_exists_gamma`

Consequently, the final permutation criterion is faithfully stated and the surrounding development compiles, but the complete theorem is not yet a sorry-free formal proof.