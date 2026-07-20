import RequestProject.DeltaSteps

open scoped BigOperators

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace GeneralizedKasami

/-
Two distinct elements in the fiber `Q⁻¹(Delta⁻¹)` have sum `Delta`.
This is statement (i), obtained by combining Steps (8) and (9).
-/
theorem pair_sum_eq_delta
    (n k : ℕ) (gamma Delta x₀ x₁ : GF n)
    (hn : 0 < n) (hcop : Nat.Coprime k n)
    (hgamma : gamma ≠ 0) (hDelta : Delta ≠ 0)
    (hdef : IsDelta n k gamma Delta)
    (hne : x₀ ≠ x₁)
    (hx₀ : (gammaPolynomial n k gamma).eval x₀ = Delta⁻¹)
    (hx₁ : (gammaPolynomial n k gamma).eval x₁ = Delta⁻¹) :
    x₀ + x₁ = Delta := by
  -- Applying `gammaPolynomial_eq_delta_inv_iff` to both fiber equations.
  have h₀ := gammaPolynomial_eq_delta_inv_iff n k gamma Delta x₀ hgamma hDelta hdef
  have h₁ := gammaPolynomial_eq_delta_inv_iff n k gamma Delta x₁ hgamma hDelta hdef;
  -- Applying `frobenius_add_eq_frobenius_add_iff` to the scaled elements.
  have h₂ := frobenius_add_eq_frobenius_add_iff n k (x₀ / Delta) (x₁ / Delta) hn hcop (by
  grind);
  grind

/-
The two elements in the fiber have the same absolute trace.
This is statement (ii), using statement (i) and Step (10).
-/
theorem pair_trace_eq
    (n k : ℕ) (gamma Delta x₀ x₁ : GF n)
    (hn : 0 < n) (hcop : Nat.Coprime k n)
    (hgamma : gamma ≠ 0) (hDelta : Delta ≠ 0)
    (hdef : IsDelta n k gamma Delta)
    (hne : x₀ ≠ x₁)
    (hx₀ : (gammaPolynomial n k gamma).eval x₀ = Delta⁻¹)
    (hx₁ : (gammaPolynomial n k gamma).eval x₁ = Delta⁻¹) :
    (∑ j ∈ Finset.range n, x₀ ^ (2 ^ j)) =
      ∑ j ∈ Finset.range n, x₁ ^ (2 ^ j) := by
  have h_sum_eq : ∑ j ∈ Finset.range n, (x₀ + x₁) ^ 2 ^ j = 0 := by
    rw [ pair_sum_eq_delta n k gamma Delta x₀ x₁ hn hcop hgamma hDelta hdef hne hx₀ hx₁ ] ; exact trace_sum_delta_eq_zero n k gamma Delta hn hgamma hDelta hdef;
  simp_all +decide [ add_pow_char_pow, Finset.sum_add_distrib ];
  grind +qlia

/-
The homogeneous version of the telescoping identity: Step (7), iterated
`kInv` times, gives the endpoint expression for the Kasami sum of `Delta`.
-/
lemma iteratedKasamiSum_delta
    (n k kInv : ℕ) (gamma Delta : GF n)
    (hn : 0 < n) (hInv : k * kInv ≡ 1 [MOD n])
    (hidentity : Delta ^ (2 ^ k) =
      gamma * Delta + (gamma * Delta) ^ (2 ^ k)) :
    iteratedKasamiSum n k kInv Delta =
      gamma * Delta + (gamma * Delta) ^ 2 := by
  unfold iteratedKasamiSum;
  -- Apply the identity iteratively to each term in the sum.
  have h_iter : ∀ i ∈ Finset.range kInv, Delta ^ (2 ^ ((i + 1) * k)) = (gamma * Delta) ^ (2 ^ (i * k)) + (gamma * Delta) ^ (2 ^ ((i + 1) * k)) := by
    intro i hi; induction i <;> simp_all +decide [ Nat.succ_mul, pow_add, pow_mul ] ;
    rename_i i hi'; rw [ hi' ( Nat.lt_of_succ_lt hi ) ] ;
    simp +decide [ add_pow_char_pow, mul_pow ];
  rw [ Finset.sum_congr rfl h_iter ];
  convert Finset.sum_range_sub ( fun i => ( gamma * Delta ) ^ 2 ^ ( i * k ) ) kInv using 1 ; norm_num [ pow_succ, pow_mul' ];
  · simp +decide [ sub_eq_add_neg, Finset.sum_add_distrib ];
    grind;
  · rw [ show kInv * k = k * kInv by ring, show ( gamma * Delta ) ^ 2 ^ ( k * kInv ) = ( gamma * Delta ) ^ 2 ^ 1 from ?_ ] ; norm_num;
    · grind;
    · convert gf_frobenius_mod n ( k * kInv ) 1 ( gamma * Delta ) hn hInv using 1

/-- The expression denoted by `e_j` when evaluated at `x_j`. -/
noncomputable def eTerm
    (n k kInv : ℕ) (a : Fin 2) (gamma x : GF n) : GF n :=
  gammaCoefficient n k gamma * x ^ (2 ^ k + 1) +
    iteratedKasamiSum n k kInv x +
    algebraMap (ZMod 2) (GF n) a *
      (∑ j ∈ Finset.range n, x ^ (2 ^ j))

/-
Statement (iii): if `x₀` and `x₁` are the two distinct elements in the
fiber `Q⁻¹(Delta⁻¹)`, then the corresponding expressions `e₀,e₁` sum to one.
-/
theorem e0_plus_e1_equals_one
    (n k kInv : ℕ) (a : Fin 2) (gamma Delta x₀ x₁ : GF n)
    (hn : 0 < n) (hcop : Nat.Coprime k n)
    (hInv : k * kInv ≡ 1 [MOD n])
    (hgamma : gamma ≠ 0) (hDelta : Delta ≠ 0)
    (hdef : IsDelta n k gamma Delta)
    (hne : x₀ ≠ x₁)
    (hx₀ : (gammaPolynomial n k gamma).eval x₀ = Delta⁻¹)
    (hx₁ : (gammaPolynomial n k gamma).eval x₁ = Delta⁻¹) :
    eTerm n k kInv a gamma x₀ + eTerm n k kInv a gamma x₁ = 1 := by
  unfold eTerm
  -- From pair_sum_eq_delta, we have x₀ + x₁ = Delta.
  have hx₀x₁ : x₀ + x₁ = Delta := by
    apply pair_sum_eq_delta n k gamma Delta x₀ x₁ hn hcop hgamma hDelta hdef hne hx₀ hx₁;
  -- From pair_trace_eq, we have ∑ j ∈ Finset.range n, x₀ ^ (2 ^ j) = ∑ j ∈ Finset.range n, x₁ ^ (2 ^ j).
  have hsum_eq : ∑ j ∈ Finset.range n, x₀ ^ (2 ^ j) = ∑ j ∈ Finset.range n, x₁ ^ (2 ^ j) := by
    apply pair_trace_eq n k gamma Delta x₀ x₁ hn hcop hgamma hDelta hdef hne hx₀ hx₁
  generalize_proofs at *; (
  -- From added Q(x₀)=Q(x₁) and using x₀+x₁=Delta gives S(x₀)+S(x₁)=S(Delta).
  have hsum_S_eq : iteratedKasamiSum n k kInv x₀ + iteratedKasamiSum n k kInv x₁ = iteratedKasamiSum n k kInv Delta := by
    simp +decide [ ← hx₀x₁, iteratedKasamiSum ];
    simp +decide [ ← Finset.sum_add_distrib, add_pow_char_pow ];
  -- From iteratedKasamiSum_delta, we have S(Delta) = gamma*Delta + (gamma*Delta)^2.
  have hsum_S_delta : iteratedKasamiSum n k kInv Delta = gamma * Delta + (gamma * Delta) ^ 2 := by
    apply iteratedKasamiSum_delta n k kInv gamma Delta hn hInv;
    convert delta_frobenius_identity n k gamma Delta hgamma hDelta hdef using 1;
  simp_all +decide [ pow_succ, mul_comm, mul_left_comm ];
  grind +splitImp);

end GeneralizedKasami