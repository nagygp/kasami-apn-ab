import Mathlib
import Dobbertin1999MVP.FiniteField.TraceNorm
import Dobbertin1999MVP.FiniteField.ExpArith
import Dobbertin1999MVP.FiniteField.FrobAlg
import Dobbertin1999MVP.FiniteField.BareLemma31Skeleton

/-!
# Adjoint Bijectivity Transfer

Engine for transferring bijectivity from L₁(x)·x^e to L₂(x)·x^l
when L₁ and L₂ are trace-adjoints and e·l ≡ 1 mod (|F|-1).
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

/-
═══════════════════════════════════════════
Adjoint swap theorem
═══════════════════════════════════════════
-/
lemma adjoint_swap_bij {n : ℕ} (hn : Fintype.card F = p ^ n) (hn1 : 1 ≤ n)
    (L₁ L₂ : F → F)
    (hL₁_add : ∀ a b, L₁ (a + b) = L₁ a + L₁ b)
    (hL₂_add : ∀ a b, L₂ (a + b) = L₂ a + L₂ b)
    (hAdj : ∀ w z, frobSum p n (L₁ w * z) = frobSum p n (w * L₂ z))
    (hTnd : ∀ x : F, x ≠ 0 → ∃ y, frobSum p n (x * y) ≠ 0)
    (e l : ℕ)
    (hel : e * l % (Fintype.card F - 1) = 1 % (Fintype.card F - 1))
    (hbij : Function.Bijective (fun x : F => L₁ x * x ^ e)) :
    Function.Bijective (fun x : F => L₂ x * x ^ l) := by
  by_cases he : e = 0
  · -- Degenerate case: e = 0
    simp [he] at hel
    have := Finset.card_eq_two.mp hel; obtain ⟨ x, y, hxy ⟩ := this; simp_all +decide [ Fintype.card_eq_one_iff ] ;
    have hL₁_zero : L₁ 0 = 0 := by
      simpa using hL₁_add 0 0
    have hL₂_zero : L₂ 0 = 0 := by
      simpa using hL₂_add 0 0
    have hL₁_one : L₁ 1 = 1 := by
      simp_all +decide [ Finset.ext_iff, Set.ext_iff ];
      cases hxy.2 0 <;> cases hxy.2 1 <;> aesop
    have hL₂_one : L₂ 1 = 1 := by
      have := hAdj 1 1; simp_all +decide [ frobSum ] ;
      rcases n with ( _ | _ | n ) <;> norm_num [ Finset.sum_range_succ' ] at *;
      · exact this.symm;
      · exact absurd hn ( ne_of_lt ( lt_of_lt_of_le ( show 2 < p ^ 2 by nlinarith only [ hp.1.two_le ] ) ( Nat.pow_le_pow_right hp.1.pos ( Nat.succ_le_succ ( Nat.succ_le_succ n.zero_le ) ) ) ) )
    simp_all +decide [ Finset.ext_iff, Set.ext_iff ];
    cases hxy.2 0 <;> cases hxy.2 1 <;> aesop ( simp_config := { singlePass := true } ) ;
  · by_cases hl : l = 0
    · simp [hl] at hel; subst hl; simp only [pow_zero, mul_one]
      exact Finite.injective_iff_bijective.mp (fun a b hab => by
        haveI : Fact (Fintype.card F = 2) := ⟨hel⟩
        exact (by
        have := @ZMod.intCast_eq_intCast_iff;
        specialize this 0 1 2 ; simp_all +decide;
        have : p = 2 := by
          have := congr_arg Even hn; norm_num [ hp.1.even_iff, parity_simps ] at this;
          exact this.1
        generalize_proofs at *; (
        subst this; rcases n with ( _ | _ | n ) <;> norm_num [ Nat.pow_succ' ] at *;
        have := Finset.card_eq_two.mp hel; obtain ⟨ x, y, hxy ⟩ := this; simp_all +decide [ Finset.ext_iff ] ;
        cases hxy.2 0 <;> cases hxy.2 1 <;> cases hxy.2 a <;> cases hxy.2 b <;> simp_all +decide only;
        all_goals subst_vars; simp_all +decide [ CharTwo.add_self_eq_zero ] ;
        · have := hL₂_add 0 1; simp_all +decide ;
          specialize hAdj 1 1 ; simp_all +decide [ frobSum ] ;
        · have := hL₂_add 1 1; simp_all +decide [ CharTwo.add_self_eq_zero ] ;
          specialize hAdj 1 1 ; simp_all +decide [ frobSum ] ;
        · have := hL₂_add 1 0; simp_all +decide ;
          specialize hAdj 1 1; simp_all +decide [ frobSum ] ;
        · have := hL₂_add 0 1; simp_all +decide ;
          specialize hAdj 1 1 ; simp_all +decide [ frobSum ])))
    · exact adjoint_swap_bij_bare p hn hn1 L₁ L₂ hL₁_add hL₂_add hAdj hTnd e l
        (Nat.pos_of_ne_zero he) (Nat.pos_of_ne_zero hl) hel hbij

end DempwolffMueller
