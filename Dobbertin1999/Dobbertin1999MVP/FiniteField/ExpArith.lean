import Mathlib

/-!
# Foundational Layer F3: Exponent Arithmetic Engine

Bijectivity of the power map `x ↦ xᵃ` when `a` is coprime to `|F| − 1`.
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

omit hp [CharP F p] in
lemma pow_field_bijective {a : ℕ} (ha : Nat.Coprime (Fintype.card F - 1) a)
    (ha_pos : 0 < a) :
    Function.Bijective (fun x : F => x ^ a) := by
  obtain ⟨b, hb⟩ : ∃ b, a * b ≡ 1 [MOD (Fintype.card F - 1)] := by
    have := Nat.exists_mul_mod_eq_one_of_coprime ha.symm;
    rcases k : Fintype.card F - 1 with ( _ | _ | k ) <;> simp_all +decide [ Nat.ModEq, Nat.mod_one ];
    grind +splitIndPred;
  have h_exp : ∀ x : F, x ≠ 0 → x ^ (a * b) = x := by
    intro x hx; rw [ ← Nat.mod_add_div ( a * b ) ( Fintype.card F - 1 ), hb ] ; simp +decide [ pow_add, pow_mul, hx ] ;
    rcases k : Fintype.card F - 1 with ( _ | _ | k ) <;> simp_all +decide [ pow_succ', mul_assoc ];
    · have := FiniteField.pow_card_sub_one_eq_one x; aesop;
    · have := FiniteField.pow_card_sub_one_eq_one x; simp_all +decide [ pow_succ', mul_assoc ] ;
  have h_inj : Function.Injective (fun x : F => x ^ a) := by
    intro x y hxy;
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp_all +decide [ pow_mul ];
    · rw [ zero_pow ha_pos.ne', eq_comm ] at hxy ; aesop;
    · cases a <;> simp_all +decide;
    · rw [ ← h_exp x hx, ← h_exp y hy, hxy ];
  exact ⟨ h_inj, Finite.injective_iff_surjective.mp h_inj ⟩

end DempwolffMueller
