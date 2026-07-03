import Mathlib

/-!
# Foundational Layer F1: Frobenius Operator Algebra

Frobenius cycling, periodicity, a linearized-trace Frobenius identity, and the
fact that Frobenius composition preserves bijectivity.  Only the pieces consumed
by the MCM → APN chain are retained.
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

-- ═══════════════════════════════════════════
-- F1.1 : Frobenius cycling
-- ═══════════════════════════════════════════

lemma frob_cycle (x : F) : x ^ Fintype.card F = x := FiniteField.pow_card x

lemma frob_mod {n : ℕ} (hn : Fintype.card F = p ^ n) (x : F) (r : ℕ) :
    x ^ (p ^ r) = x ^ (p ^ (r % n)) := by
  conv_lhs => rw [show r = n * (r / n) + r % n from (Nat.div_add_mod r n).symm,
    pow_add, pow_mul]
  have : ∀ k : ℕ, x ^ (p ^ (n * k)) = x := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [Nat.mul_succ, pow_add, pow_mul, ← hn, frob_cycle, ih]
  rw [this]

-- ═══════════════════════════════════════════
-- F1.2 : Frobenius as ring homomorphism
-- ═══════════════════════════════════════════

lemma finset_sum_frob_eq {ι : Type*} (s : Finset ι) (f : ι → F) (r : ℕ) :
    (∑ i ∈ s, f i) ^ (p ^ r) = ∑ i ∈ s, (f i) ^ (p ^ r) := by
  simp_rw [← show ∀ x : F, (iterateFrobenius F p r) x = x ^ (p ^ r) from
    fun x => by simp [iterateFrobenius]]
  rw [← map_sum]

-- ═══════════════════════════════════════════
-- F1.3 : Frobenius on the linearized trace (output)
-- ═══════════════════════════════════════════

lemma truncTrace_frob_output_general (m : ℕ) (x : F) (s : ℕ) :
    (∑ i ∈ Finset.range m, x ^ (p ^ i)) ^ (p ^ s) =
    ∑ i ∈ Finset.range m, x ^ (p ^ (i + s)) := by
  induction m with
  | zero => simp [zero_pow (Nat.pos_of_ne_zero (pow_ne_zero s hp.out.ne_zero)).ne']
  | succ m ih =>
    rw [Finset.sum_range_succ, add_pow_char_pow (p := p) (n := s), ih,
        Finset.sum_range_succ, ← pow_mul, ← pow_add]

-- ═══════════════════════════════════════════
-- F1.4 : Frobenius preserves bijection
-- ═══════════════════════════════════════════

lemma frob_bijective (r : ℕ) : Function.Bijective (fun x : F => x ^ (p ^ r)) :=
  ⟨iterateFrobenius_inj F p r,
   (Finite.injective_iff_surjective).mp (iterateFrobenius_inj F p r)⟩

lemma frob_comp_bijective_right {f : F → F} (hf : Function.Bijective f) (r : ℕ) :
    Function.Bijective (fun x : F => (f x) ^ (p ^ r)) :=
  (frob_bijective p r).comp hf

-- ═══════════════════════════════════════════
-- F1.5 : Fermat's little theorem for power maps
-- ═══════════════════════════════════════════

lemma pow_card_sub_one_eq_one' {x : F} (hx : x ≠ 0) :
    x ^ (Fintype.card F - 1) = 1 :=
  FiniteField.pow_card_sub_one_eq_one x hx

end DempwolffMueller
