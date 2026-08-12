# Dependency Graph: `mcm_isPermutation`

This graph describes the proof of `GeneralizedKasami.mcm_isPermutation` in
[AristotleGPT56TerraNagyGP/RequestProject/genMCM.lean](AristotleGPT56TerraNagyGP/RequestProject/genMCM.lean).

The theorem specializes Dobbertin's Theorem 4 to `beta = 0`.  Its hypotheses
that `k` is odd and coprime to `n` are used to construct a modular inverse
`kInv`, the quotient `nPrime`, and a parity witness `a : Fin 2`.  Those data
supply the hypotheses of `dobbertin_theorem4`, from which the final MCM
permutation-polynomial component is extracted.

```mermaid
flowchart TD
  Goal["mcm_isPermutation\nP_0 is a permutation polynomial"]

  Coprime["hcop : Coprime k n"]
  Odd["hkOdd : k % 2 = 1"]
  Bounds["hn, hk, hkn\n0 < n; 0 < k; k < n"]

  Inverse["Nat.exists_mul_mod_eq_one_of_coprime\nconstruct kInv"]
  NPrime["nPrime := (kInv * k) / n"]
  Product["hprod\nkInv * k = nPrime * n + 1"]
  A["a : Fin 2\na.val = nPrime mod 2"]
  InversePos["hInvPos : 0 < kInv"]
  KMod["hkMod : k = 1 (mod 2)"]
  QParity["hqpar\nkInv + a*n = 1 (mod 2)"]
  BetaParity["hbeta\n0 = nPrime + a*k (mod 2)"]

  Theorem4["dobbertin_theorem4\nDobbertin Theorem 4"]
  Extract["extract .2.2.2.2.2\nIsPermutationPolynomial (genMCMpol n k 0)"]

  Coprime --> Inverse
  Inverse --> NPrime
  Inverse --> Product
  NPrime --> Product
  Inverse --> InversePos
  Odd --> KMod
  NPrime --> A
  Product --> QParity
  A --> QParity
  KMod --> QParity
  Product --> BetaParity
  A --> BetaParity
  KMod --> BetaParity

  Bounds --> Theorem4
  Coprime --> Theorem4
  Product --> Theorem4
  InversePos --> Theorem4
  Inverse --> Theorem4
  QParity --> Theorem4
  BetaParity --> Theorem4
  Theorem4 --> Extract --> Goal
```

## Dependencies of `dobbertin_theorem4`

```mermaid
flowchart TD
  T4["dobbertin_theorem4"]

  Transfer["transfer_maps_inverse\npsi_beta and phi_alpha are mutual inverses"]
  Forward["genKasami_comp_psi_eq_genMCM\nq_a o psi_b = inversion o P_b"]
  Reverse["genMCM_comp_phi_eq_genKasami\nP_b o phi_a = inversion o q_a"]
  KasamiPerm["parity_implies_permutation\nq_a is bijective under the parity condition"]
  Finite["Finite.injective_iff_surjective\nfinite-field injectivity/surjectivity"]

  T4 --> Transfer
  T4 --> Forward
  T4 --> Reverse
  T4 --> KasamiPerm
  T4 --> Finite

  Transfer --> Frob["gf_frobenius_pow_card"]
  Transfer --> Trace["trace_sum_frobenius"]
  Transfer --> CharSum["sum_pow_char_pow"]

  Forward --> Transfer
  Forward --> Div["genMCMeval_eq_div"]
  Forward --> EvalEq["evaluation_eq_iff_equation_of_ne_zero"]
  Reverse --> Transfer
  Reverse --> Forward

  Div --> Formula["genMCMeval_formula"]
  Div --> Frob
  Formula --> TracePoly["tracePolynomial"]

  KasamiPerm --> Unique["kasamiEquation_unique"]
  KasamiPerm --> EvalEq
  KasamiPerm --> ZeroEq["evaluation_eq_zero_iff_equation"]
```

## How `parity_implies_permutation` Proves Kasami Bijectivity

The odd-parity hypothesis is the mechanism that rules out a zero value of
the auxiliary gamma polynomial.  This permits uniqueness of each admissible
Kasami-equation fiber.  The lemma first proves injectivity of the Kasami
evaluation map, then converts injectivity to bijectivity because `GF(2^n)` is
finite.

```mermaid
flowchart TD
  Parity["hparity\nkInv + a*n = 1 (mod 2)"]
  Input["hn, hk, hkn, hInvPos, hInvLt\nhcop and hInv"]
  Perm["parity_implies_permutation\nIsPermutationPolynomial (genKasamiPol ...)"]
  Inj["h_inj\ninjectivity of Kasami evaluation"]
  Finite["Finite.injective_iff_surjective\nfinite field"]

  SameEval["Assume q_a(x) = q_a(y)"]
  ZeroCases{"x = 0 or y = 0?"}
  ZeroFiber["evaluation_eq_zero_iff_equation\nreduce zero-value cases"]
  NonzeroFiber["evaluation_eq_iff_equation_of_ne_zero\ntranslate both evaluations"]
  Unique["kasamiEquation_unique\nadmissible solutions are unique"]
  Equal["x = y"]

  ZeroC{"c = 0?"}
  RhsZero["equationRHS_eq_zero_unique"]
  Gamma{"exists gamma, c = gamma^(2^k+1) + gamma?"}
  GammaCase["kasamiEquation_unique_of_exists_gamma"]
  LinearCase["linearized_unique_of_not_exists_gamma"]

  GammaCase --> Delta["exists_delta"]
  Delta --> Ell["ell_eval_eq_zero_iff_gammaPolynomial"]
  Parity --> NoZero["kasamiEquation_not_gammaPolynomial_zero"]
  NoZero --> GammaCase
  GammaCase --> Pair["e0_plus_e1_equals_one"]
  Pair --> GammaUnique["contradiction from eTerm = 0\nfor both candidate roots"]

  Input --> Perm
  Parity --> Perm
  Perm --> Inj --> Finite --> Perm
  SameEval --> ZeroCases
  ZeroCases --> ZeroFiber --> Unique
  ZeroCases --> NonzeroFiber --> Unique
  Unique --> Equal --> Inj
  Parity --> Unique
  Input --> Unique
  Unique --> ZeroC
  ZeroC --> RhsZero
  ZeroC --> Gamma
  Gamma --> GammaCase
  Gamma --> LinearCase
  RhsZero --> Equal
  GammaUnique --> GammaCase
  GammaCase --> Equal
  LinearCase --> Equal
```

## Source Map

- The target theorem and the transfer-map/MCM identities are in [AristotleGPT56TerraNagyGP/RequestProject/genMCM.lean](AristotleGPT56TerraNagyGP/RequestProject/genMCM.lean).
- The Kasami permutation branch is in [AristotleGPT56TerraNagyGP/RequestProject/genkasamipol.lean](AristotleGPT56TerraNagyGP/RequestProject/genkasamipol.lean): `parity_implies_permutation` reduces injectivity to `kasamiEquation_unique`; the new third diagram expands this proof.
- Field and trace identities, including `evaluation_eq_iff_equation_of_ne_zero`, `trace_sum_frobenius`, and `gf_frobenius_pow_card`, are in [AristotleGPT56TerraNagyGP/RequestProject/basic.lean](AristotleGPT56TerraNagyGP/RequestProject/basic.lean).
- The modular-inverse existence theorem, parity arithmetic, finite-function equivalences, and characteristic-power sum lemma are from Mathlib.

The first diagram tracks the actual specialization proof.  The second expands the principal theorem call enough to show why the result ultimately rests on the Kasami permutation argument and Frobenius/trace algebra, without reproducing every internal calculation in the long transfer-map proof.
