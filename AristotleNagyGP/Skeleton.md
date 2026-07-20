# Proof skeleton for `generalizedKasami_isPermutation_iff`

## Statement and notation

Work in the finite field

\[
F=\operatorname{GF}(2^n),
\]

with positive integers `k,n`, where `k<n` and `gcd(k,n)=1`.  The natural
number `kInv` is the chosen representative of the inverse of `k` modulo `n`:

\[
k\,k'\equiv 1\pmod n,\qquad 1\leq k'<n.
\]

The parameter `a : Fin 2` represents \(\alpha\in\{0,1\}\).  The development
keeps separate:

* `genKasamiPol n k kInv a`, the polynomial \(q_\alpha\), and
* `genKasamiEval n k kInv a`, the function obtained by evaluating that
  polynomial on \(F\).

`IsPermutationPolynomial p` means that `p.eval` is bijective.  The main
result is

```lean
theorem generalizedKasami_isPermutation_iff ... :
    IsPermutationPolynomial (genKasamiPol n k kInv a) ↔
      kInv + a.val * n ≡ 1 [MOD 2]
```

Thus the mathematical condition is that \(k'+\alpha n\) is odd.

## 1. Rewrite polynomial fibers as a Kasami equation

Define

\[
R(x)=\sum_{i=1}^{k'}x^{2^{ik}}+
      \alpha\sum_{j=0}^{n-1}x^{2^j}.
\]

This is `equationRHS`.  For `x ≠ 0`, the equation

\[
q_\alpha(x)=c
\]

is equivalent to

\[
c x^{2^k+1}=R(x). \tag{K}
\]

This is proved by `evaluation_eq_iff_equation_of_ne_zero`: multiply the
polynomial evaluation by \(x^{2^k+1}\) and use
\(x^{2^n-1}=1\).  The zero fiber is handled separately by
`evaluation_eq_zero_iff_equation`.

Consequently, it is enough to show that under the odd-parity condition every
admissible fiber equation (K) has at most one solution.

## 2. Necessity of the parity condition

The forward implication is `permutation_implies_parity`.

If \(k'+\alpha n\) is even, direct evaluation gives

\[
q_\alpha(0)=q_\alpha(1)=0.
\]

Since \(0\neq1\) in \(F\), the evaluation function is not injective and hence
cannot be a permutation.  Therefore a permutation polynomial must satisfy

\[
k'+\alpha n\equiv1\pmod2.
\]

## 3. Frobenius and trace identities

The converse uses several characteristic-two identities.

* `gf_frobenius_mod`: \(x^{2^r}\) depends only on \(r\bmod n\).
* `trace_sum_frobenius`: the absolute trace sum is invariant under every
  Frobenius map.
* `kasami_sum_frobenius`: raising
  \(\sum_{i=1}^{k'}x^{2^{ik}}\) to the \(2^k\)-th power shifts the summation
  endpoints.  The congruence \(kk'\equiv1\pmod n\) identifies the final
  endpoint.

Applying these identities to (K) shows that every nonzero solution of (K)
is a root of the affine linearized polynomial

\[
\ell_c(X)=c^{2^k}X^{2^{2k}}+X^{2^k}+cX+1.
\]

This reduction is `kasamiEquation_implies_linearized`.

The zero fiber is also controlled here: `equationRHS_eq_zero_unique` proves
that, under odd parity,

\[
R(x)=0 \quad\Longrightarrow\quad x=0.
\]

## 4. First case: `c` is not of gamma form

Split according to whether

\[
c=\gamma^{2^k+1}+\gamma
\]

for some \(\gamma\in F\).

If no such \(\gamma\) exists, `linearized_unique_of_not_exists_gamma` proves
that \(\ell_c\) has at most one root.  Its key input is the factorization
`ell_0_eval_factorization` for the homogeneous polynomial
\(\ell_{0,c}=\ell_c+1\).  If two roots existed, their difference would be a
nonzero root of \(\ell_{0,c}\); the factorization would then construct a
\(\gamma\) satisfying \(c=\gamma^{2^k+1}+\gamma\), contradicting the case
assumption.

Thus (K) has at most one admissible solution in this case.

## 5. Second case: `c` has gamma form

Now suppose

\[
c=\gamma^{2^k+1}+\gamma.
\]

The subcase \(\gamma=0\) reduces to the already established uniqueness of the
zero fiber.  Assume henceforth that \(\gamma\neq0\).

### 5.1 Introduce `Q` and `Delta`

Define

\[
Q(X)=cX^{2^k}+\gamma^2X+\gamma.
\]

This is `gammaPolynomial`.  Choose a nonzero \(\Delta\) satisfying

\[
(\Delta^{2^k-1})^{-1}=\gamma^{2^k-1}+\gamma^{-1}.
\]

Existence is `exists_delta`; it uses

\[
\gcd(2^k-1,2^n-1)=1,
\]

which follows from `gcd(k,n)=1`.  The defining equation yields

\[
\Delta^{2^k}=\gamma\Delta+(\gamma\Delta)^{2^k}
\]

by `delta_frobenius_identity`.

### 5.2 Factor the zero set of `ell`

`ell_eval_eq_gammaPolynomial_frobenius` expresses \(\ell_c(x)\) as

\[
Q(x)^{2^k}+(\Delta^{2^k-1})^{-1}Q(x).
\]

Because exponentiation by \(2^k-1\) is injective on the multiplicative group
of \(F\), `ell_eval_eq_zero_iff_gammaPolynomial` obtains

\[
\ell_c(x)=0
\quad\Longleftrightarrow\quad
Q(x)=0\ \text{or}\ Q(x)=\Delta^{-1}. \tag{F}
\]

### 5.3 Exclude the fiber `Q(x)=0`

For a root of `Q`, the Frobenius recurrence telescopes.  The trace recurrence
and the iterated Kasami sum give `gammaPolynomial_root_final_identity`:

\[
c x^{2^k+1}+
\sum_{i=1}^{k'}x^{2^{ik}}+
\alpha\operatorname{Tr}(x)
=	ext{the prime-field image of }(k'+\alpha n).
\]

If `x` also solves (K), the left side is zero
(`eTerm_eq_zero_of_kasamiEquation`).  Under odd parity the right side is one
(`parity_algebraMap_eq_one`), a contradiction.  Hence a solution of (K)
cannot lie in the `Q(x)=0` branch of (F).  This is
`kasamiEquation_not_gammaPolynomial_zero`.

### 5.4 Prove uniqueness in the fiber `Q(x)=Delta⁻¹`

Suppose distinct solutions \(x_0,x_1\) both satisfy

\[
Q(x_j)=\Delta^{-1}.
\]

The equation is converted by `gammaPolynomial_eq_delta_inv_iff` into one for
the linearized map \(u\mapsto u^{2^k}+u\).  Since `gcd(k,n)=1`, the kernel of
this map is exactly \(\{0,1\}\), formalized by
`frobenius_add_eq_frobenius_add_iff`.  Therefore:

1. `pair_sum_eq_delta` gives \(x_0+x_1=\Delta\).
2. `trace_sum_delta_eq_zero` and `pair_trace_eq` show
   \(\operatorname{Tr}(x_0)=\operatorname{Tr}(x_1)\).
3. The Kasami sums telescope using `iteratedKasamiSum_delta`.

Combining these identities, `e0_plus_e1_equals_one` proves that the two
expressions associated with (K) satisfy

\[
e(x_0)+e(x_1)=1.
\]

But each solution of (K) has \(e(x_j)=0\).  This contradiction proves
`kasamiEquation_unique_of_exists_gamma`.

## 6. Assemble uniqueness for every fiber

`kasamiEquation_unique` combines the cases:

* `c=0`: use `equationRHS_eq_zero_unique`;
* `c≠0` and no gamma representation: use
  `linearized_unique_of_not_exists_gamma`;
* `c≠0` and a gamma representation: use
  `kasamiEquation_unique_of_exists_gamma`.

The admissibility hypotheses in this lemma ensure that solutions are nonzero
when `c ≠ 0`, because (K) itself always has the formal solution `x=0` unless
one keeps track of its correspondence with an actual polynomial fiber.

## 7. From fiber uniqueness to bijectivity

In `parity_implies_permutation`, suppose

\[
q_\alpha(x)=q_\alpha(y).
\]

The proof separates the zero and nonzero cases, translates the equality into
Kasami equations using the lemmas from Step 1, and applies
`kasamiEquation_unique`.  Thus the evaluation function is injective.  Since
`GF(2^n)` is finite, injectivity implies surjectivity, so the function is
bijective and `genKasamiPol` is a permutation polynomial.

Finally, `generalizedKasami_isPermutation_iff` joins:

* `permutation_implies_parity`, and
* `parity_implies_permutation`.

The companion theorem `evaluation_bijective_iff` restates the result directly
for the separately defined function `genKasamiEval`.

## Lean-file roadmap

* `RequestProject/basic.lean`: definitions, fiber reduction, Frobenius/trace
  identities, the linearized polynomial, the first gamma case, and zero-fiber
  uniqueness.
* `RequestProject/GammaSteps.lean`: `Q`, its root recurrence, trace identity,
  and telescoping Kasami identity.
* `RequestProject/DeltaSteps.lean`: construction and properties of `Delta`.
* `RequestProject/PairSteps.lean`: identities for two elements in the
  `Q(x)=Delta⁻¹` fiber.
* `RequestProject/EllSteps.lean`: factorization of the zero set of `ell`
  through `Q`.
* `RequestProject/genkasamipol.lean`: final uniqueness argument, bijectivity,
  and `generalizedKasami_isPermutation_iff`.
