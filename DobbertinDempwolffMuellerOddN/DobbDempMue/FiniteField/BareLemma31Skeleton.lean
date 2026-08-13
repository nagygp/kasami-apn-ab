import Mathlib
import DobbDempMue.FiniteField.TraceNorm
import DobbDempMue.FiniteField.ExpArith
import DobbDempMue.FiniteField.FrobAlg

/-!
# Bare-Function Lemma 3.1

Reproves the core Lemma 3.1 argument for bare additive functions F → F
and frobSum as the trace form, avoiding LinearMap wrapping.
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

-- ═══════════════════════════════════════════
-- Definitions
-- ═══════════════════════════════════════════

/-- Δ_{L,M,y}(x) = L(x·y) · M(y). -/
def DeltaBare' (L : F → F) (M : F → F) (y : F) (x : F) : F := L (x * y) * M y

-- ═══════════════════════════════════════════
-- Helper lemmas
-- ═══════════════════════════════════════════

lemma DeltaBare_sub_additive' (L : F → F) (hL_add : ∀ a b, L (a + b) = L a + L b)
    (M : F → F) (y₁ y₂ : F) (a b : F) :
    (DeltaBare' L M y₁ (a + b) - DeltaBare' L M y₂ (a + b)) =
    (DeltaBare' L M y₁ a - DeltaBare' L M y₂ a) +
    (DeltaBare' L M y₁ b - DeltaBare' L M y₂ b) := by
  unfold DeltaBare'; rw [add_mul, add_mul, hL_add, hL_add]; ring

lemma DeltaBare_sub_zero_imp_zero'
    (L M : F → F)
    (hM_mul : ∀ a b, M (a * b) = M a * M b)
    (hM_inj : Function.Injective M)
    (hP_inj : Function.Injective (fun x => L x * M x))
    {y₁ y₂ : F} (hy : y₁ ≠ y₂) {x : F}
    (h : DeltaBare' L M y₁ x = DeltaBare' L M y₂ x) : x = 0 := by
  contrapose! hP_inj;
  simp_all +decide [ Function.Injective, DeltaBare' ];
  grind +splitIndPred

lemma P_inj_imp_DeltaBare_sub_bij' (L : F → F)
    (hL_add : ∀ a b, L (a + b) = L a + L b)
    (M : F → F)
    (hM_mul : ∀ a b, M (a * b) = M a * M b)
    (hM_inj : Function.Injective M)
    (hP_inj : Function.Injective (fun x => L x * M x))
    {y₁ y₂ : F} (hy : y₁ ≠ y₂) :
    Function.Bijective (fun x => DeltaBare' L M y₁ x - DeltaBare' L M y₂ x) := by
  have h_inj : Function.Injective (fun x => DeltaBare' L M y₁ x - DeltaBare' L M y₂ x) := by
    intro a b hab;
    have := DeltaBare_sub_additive' L hL_add M y₁ y₂ ( b - a ) a; simp_all +decide [ sub_eq_iff_eq_add ] ;
    have := DeltaBare_sub_zero_imp_zero' L M hM_mul hM_inj hP_inj hy this; simp_all +decide [ sub_eq_iff_eq_add ] ;
  exact Finite.injective_iff_bijective.mp h_inj

lemma DeltaBare_sub_bij_imp_P_inj' (L : F → F)
    (hL_add : ∀ a b, L (a + b) = L a + L b) (hL0 : L 0 = 0)
    (M : F → F) (hM_mul : ∀ a b, M (a * b) = M a * M b)
    (hM_inj : Function.Injective M)
    (hDelta : ∀ y₁ y₂ : F, y₁ ≠ y₂ →
      Function.Bijective (fun x => DeltaBare' L M y₁ x - DeltaBare' L M y₂ x)) :
    Function.Injective (fun x => L x * M x) := by
  intro a b hab;
  by_cases h : a = b <;> simp_all +decide [ sub_eq_iff_eq_add ];
  obtain ⟨x, hx⟩ : ∃ x : F, DeltaBare' L M a x - DeltaBare' L M b x = 0 := by
    replace hDelta := congr_arg Multiset.toFinset ( hDelta a b h ) ; rw [ Finset.ext_iff ] at hDelta ; specialize hDelta 0 ; aesop;
  have := hDelta a b h; replace := Fintype.bijective_iff_injective_and_card ( fun x => DeltaBare' L M a x - DeltaBare' L M b x ) ; simp_all +decide [ sub_eq_iff_eq_add ] ;
  have := @this 1 0; simp_all +decide [ sub_eq_iff_eq_add ] ;
  simp_all +decide [ DeltaBare' ]

lemma DeltaBare_trace_adjoint' {n : ℕ} (hn : Fintype.card F = p ^ n)
    (L₁ L₂ : F → F)
    (hAdj : ∀ w z, frobSum p n (L₁ w * z) = frobSum p n (w * L₂ z))
    (M Minv : F → F) (hM_mul : ∀ a b, M (a * b) = M a * M b)
    (hMinv_left : ∀ x, Minv (M x) = x) (u v y : F) :
    frobSum p n (DeltaBare' L₁ M y u * v) =
    frobSum p n (u * DeltaBare' L₂ Minv (M y) v) := by
  have h_eq : frobSum p n (L₁ (u * y) * (v * M y)) = frobSum p n ((u * y) * L₂ (v * M y)) := by
    simpa only [ mul_comm ] using hAdj ( u * y ) ( v * M y );
  convert h_eq using 1 <;> simp +decide [ DeltaBare' ] ; ring;
  grind +revert

lemma additive_bij_iff_adj_bij' {n : ℕ} (hn : Fintype.card F = p ^ n) (hn1 : 1 ≤ n)
    (A Aadj : F → F)
    (hA_add : ∀ a b, A (a + b) = A a + A b)
    (hAadj_add : ∀ a b, Aadj (a + b) = Aadj a + Aadj b)
    (hTadj : ∀ x y, frobSum p n (A x * y) = frobSum p n (x * Aadj y))
    (hTnd : ∀ x : F, x ≠ 0 → ∃ y, frobSum p n (x * y) ≠ 0) :
    Function.Bijective A ↔ Function.Bijective Aadj := by
  constructor;
  · intro hA_bijective
    have hA_injective : Function.Injective A := by
      exact hA_bijective.injective
    have hAadj_injective : Function.Injective Aadj := by
      intro x y hxy
      by_contra h_neq
      have h_contra : ∀ z : F, frobSum p n (A z * (x - y)) = 0 := by
        have := hAadj_add ( x - y ) y; simp_all +decide [ sub_eq_iff_eq_add ] ;
        exact frobSum_zero _ _;
      obtain ⟨ z, hz ⟩ := hTnd ( x - y ) ( sub_ne_zero.mpr h_neq );
      obtain ⟨ w, rfl ⟩ := hA_bijective.2 z; specialize h_contra w; simp_all +decide [ mul_comm ] ;
    have hAadj_surjective : Function.Surjective Aadj := by
      exact Finite.injective_iff_surjective.mp hAadj_injective
    exact ⟨hAadj_injective, hAadj_surjective⟩;
  · intro hAadj_bijective
    have hA_injective : Function.Injective A := by
      intro x y hxy;
      have h_diff_zero : ∀ z : F, frobSum p n ((x - y) * Aadj z) = 0 := by
        intro z
        have := hTadj x z
        have := hTadj y z
        simp_all +decide [ sub_mul ];
        have := frobSum_add p n ( x * Aadj z - y * Aadj z ) ( y * Aadj z ) ; simp_all +decide [ sub_mul ] ;
      exact Classical.not_not.1 fun h => by obtain ⟨ z, hz ⟩ := hTnd ( x - y ) ( sub_ne_zero_of_ne h ) ; obtain ⟨ w, rfl ⟩ := hAadj_bijective.2 z; exact hz ( h_diff_zero w ) ;
    exact ⟨hA_injective, Finite.injective_iff_surjective.mp hA_injective⟩

lemma DeltaBare_sub_bij_iff_adj' {n : ℕ} (hn : Fintype.card F = p ^ n) (hn1 : 1 ≤ n)
    (L₁ L₂ : F → F)
    (hL₁_add : ∀ a b, L₁ (a + b) = L₁ a + L₁ b)
    (hL₂_add : ∀ a b, L₂ (a + b) = L₂ a + L₂ b)
    (hAdj : ∀ w z, frobSum p n (L₁ w * z) = frobSum p n (w * L₂ z))
    (hTnd : ∀ x : F, x ≠ 0 → ∃ y, frobSum p n (x * y) ≠ 0)
    (M Minv : F → F) (hM_mul : ∀ a b, M (a * b) = M a * M b)
    (hMinv_left : ∀ x, Minv (M x) = x) (y₁ y₂ : F) :
    Function.Bijective (fun x => DeltaBare' L₁ M y₁ x - DeltaBare' L₁ M y₂ x) ↔
    Function.Bijective (fun x => DeltaBare' L₂ Minv (M y₁) x - DeltaBare' L₂ Minv (M y₂) x) := by
  have h_adj : ∀ u v : F, frobSum p n ((DeltaBare' L₁ M y₁ u - DeltaBare' L₁ M y₂ u) * v) =
    frobSum p n (u * (DeltaBare' L₂ Minv (M y₁) v - DeltaBare' L₂ Minv (M y₂) v)) := by
      intros u v; simp +decide [ sub_mul, mul_sub, * ] ;
      have h_diff : frobSum p n (DeltaBare' L₁ M y₁ u * v) = frobSum p n (u * DeltaBare' L₂ Minv (M y₁) v) ∧ frobSum p n (DeltaBare' L₁ M y₂ u * v) = frobSum p n (u * DeltaBare' L₂ Minv (M y₂) v) := by
        exact ⟨ DeltaBare_trace_adjoint' p hn L₁ L₂ hAdj M Minv hM_mul hMinv_left u v y₁, DeltaBare_trace_adjoint' p hn L₁ L₂ hAdj M Minv hM_mul hMinv_left u v y₂ ⟩;
      have h_diff : ∀ a b : F, frobSum p n (a - b) = frobSum p n a - frobSum p n b := by
        intros a b; exact (by
        convert frobSum_add p n a ( -b ) using 1 ; simp +decide [ sub_eq_add_neg ];
        rw [ sub_eq_add_neg, frobSum_neg ]);
      aesop;
  apply additive_bij_iff_adj_bij';
  any_goals tauto;
  · intro a b; simp +decide [ DeltaBare', hL₁_add, hL₂_add ] ; ring;
    rw [ hL₁_add, hL₁_add ] ; ring;
  · grind +suggestions

/-
═══════════════════════════════════════════
Main theorem
═══════════════════════════════════════════
-/
theorem adjoint_swap_bij_bare {n : ℕ} (hn : Fintype.card F = p ^ n) (hn1 : 1 ≤ n)
    (L₁ L₂ : F → F)
    (hL₁_add : ∀ a b, L₁ (a + b) = L₁ a + L₁ b)
    (hL₂_add : ∀ a b, L₂ (a + b) = L₂ a + L₂ b)
    (hAdj : ∀ w z, frobSum p n (L₁ w * z) = frobSum p n (w * L₂ z))
    (hTnd : ∀ x : F, x ≠ 0 → ∃ y, frobSum p n (x * y) ≠ 0)
    (e l : ℕ) (he_pos : 0 < e) (hl_pos : 0 < l)
    (hel : e * l % (Fintype.card F - 1) = 1 % (Fintype.card F - 1))
    (hbij : Function.Bijective (fun x : F => L₁ x * x ^ e)) :
    Function.Bijective (fun x : F => L₂ x * x ^ l) := by
  have hM_mul : ∀ a b : F, a ^ e * b ^ e = (a * b) ^ e := by
    exact fun a b => by rw [ mul_pow ] ;
  have hMinv_left : ∀ x : F, x ≠ 0 → (x ^ e) ^ l = x := by
    intro x hx_nonzero
    have h_exp : x ^ (e * l) = x := by
      rw [ ← Nat.mod_add_div ( e * l ) ( Fintype.card F - 1 ), hel ] ; simp +decide [ pow_add, pow_mul, pow_one, hx_nonzero, pow_card_sub_one_eq_one' ] ; ring;
      rcases k : Fintype.card F - 1 with ( _ | _ | k ) <;> simp_all +decide [ Nat.mod_eq_of_lt ];
      have := FiniteField.pow_card_sub_one_eq_one x; simp_all +decide ;
    simp_all +decide [ pow_mul ]
  have hM_bijective : Function.Bijective (fun x : F => x ^ e) := by
    apply pow_field_bijective;
    · refine' Nat.Coprime.symm ( Nat.Coprime.coprime_dvd_left ( dvd_mul_right e l ) _ );
      rw [ ← Nat.mod_add_div ( e * l ) ( Fintype.card F - 1 ), hel ];
      rcases k : Fintype.card F - 1 with ( _ | _ | k ) <;> simp_all +decide [ Nat.mod_eq_of_lt ];
    · exact he_pos
  have hP_inj : Function.Injective (fun x : F => L₁ x * x ^ e) := by
    exact hbij.injective
  have hDelta_bij : ∀ y₁ y₂ : F, y₁ ≠ y₂ → Function.Bijective (fun x => DeltaBare' L₁ (fun x => x ^ e) y₁ x - DeltaBare' L₁ (fun x => x ^ e) y₂ x) := by
    apply_rules [ P_inj_imp_DeltaBare_sub_bij' ];
    · exact fun a b => by rw [ mul_pow ] ;
    · exact hM_bijective.injective
  have hDelta_bij_adj : ∀ y₁ y₂ : F, y₁ ≠ y₂ → Function.Bijective (fun x => DeltaBare' L₂ (fun x => x ^ l) (y₁ ^ e) x - DeltaBare' L₂ (fun x => x ^ l) (y₂ ^ e) x) := by
    intros y₁ y₂ hy_ne
    have hDelta_bij_adj : Function.Bijective (fun x => DeltaBare' L₁ (fun x => x ^ e) y₁ x - DeltaBare' L₁ (fun x => x ^ e) y₂ x) := hDelta_bij y₁ y₂ hy_ne
    have hDelta_bij_adj' : Function.Bijective (fun x => DeltaBare' L₂ (fun x => x ^ l) (y₁ ^ e) x - DeltaBare' L₂ (fun x => x ^ l) (y₂ ^ e) x) := by
      convert DeltaBare_sub_bij_iff_adj' p hn hn1 L₁ L₂ hL₁_add hL₂_add hAdj hTnd ( fun x => x ^ e ) ( fun x => x ^ l ) _ _ y₁ y₂ using 1 <;> simp +decide [ DeltaBare' ];
      · have := hDelta_bij y₁ y₂ hy_ne; have := this.2; simp_all +decide [ DeltaBare' ] ;
      · grind;
      · exact fun x => if hx : x = 0 then by simp +decide [ hx, he_pos.ne', hl_pos.ne' ] else hMinv_left x hx
    exact hDelta_bij_adj'
  have hP2_inj : Function.Injective (fun x : F => L₂ x * x ^ l) := by
    apply DeltaBare_sub_bij_imp_P_inj' L₂ hL₂_add (by
    simpa using hL₂_add 0 0) (fun x => x ^ l) (by
    simp +decide [ mul_pow ]) (by
    intro x y hxy
    have h_eq : (x ^ e) ^ l = (y ^ e) ^ l := by
      convert congr_arg ( · ^ e ) hxy using 1 <;> ring
    have h_eq' : x = y := by
      by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp_all +decide [ pow_eq_zero_iff' ];
      · cases l <;> aesop;
      · grind +extAll
    exact h_eq') (by
    intro y₁ y₂ hy
    obtain ⟨y₁', hy₁'⟩ : ∃ y₁', y₁' ^ e = y₁ := by
      exact hM_bijective.surjective y₁
    obtain ⟨y₂', hy₂'⟩ : ∃ y₂', y₂' ^ e = y₂ := by
      exact hM_bijective.surjective y₂
    have hy₁₂' : y₁' ≠ y₂' := by
      grind
    have := hDelta_bij_adj y₁' y₂' hy₁₂'
    aesop)
  exact ⟨hP2_inj, Finite.injective_iff_surjective.mp hP2_inj⟩

end DempwolffMueller
