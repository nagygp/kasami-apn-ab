import Mathlib

/-!
# Kasami Exponent and Core Definitions

Unified definitions for the Kasami power function analysis.

## Definitions
- `kasamiExp k`:  Kasami exponent `2^{2k} − 2^k + 1`
- `L k x`:        Linearized polynomial `x^{2^k} + x`
- `Cross k s P`:  Cross form `s · P^{2^k} + s^{2^k} · P`
- `N k x`:        Norm `x^{2^k + 1}`
- `sVal k t`:     Differential value `(t+1)^d + t^d`

## Naming
The Kasami exponent was previously defined separately as both
`CollisionAnalysis.d` and `KasamiAPN.kasamiExp`. This module
provides a single unified definition.
-/

namespace CollisionAnalysis

open Fintype

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- The Kasami exponent: `d(k) = 2^{2k} − 2^k + 1`. -/
def d (k : ℕ) : ℕ := 2 ^ (2 * k) - 2 ^ k + 1

/-- The linearized polynomial `L(x) = x^{2^k} + x`. -/
def L (k : ℕ) (x : F) : F := x ^ (2 ^ k) + x

/-- The cross form `Cross(s, P) = s · P^{2^k} + s^{2^k} · P`. -/
def Cross (k : ℕ) (s P : F) : F := s * P ^ (2 ^ k) + s ^ (2 ^ k) * P

/-- The norm map `N(x) = x^{2^k + 1}`. -/
def N (k : ℕ) (x : F) : F := x ^ (2 ^ k + 1)

/-- The differential value `sVal(t) = (t+1)^d + t^d`. -/
def sVal (k : ℕ) (t : F) : F := (t + 1) ^ d k + t ^ d k

theorem d_pos (k : ℕ) (_hk : k ≥ 1) : 0 < d k := by unfold d; omega

theorem d_mul_gold (k : ℕ) (hk : k ≥ 1) : d k * (2 ^ k + 1) = 2 ^ (3 * k) + 1 := by
  unfold d; zify; rw [Nat.cast_sub (by gcongr <;> linarith)]; push_cast; ring

end CollisionAnalysis

-- Compatibility alias: KasamiAPN.kasamiExp = CollisionAnalysis.d
namespace KasamiAPN

/-- The Kasami exponent d = 2^{2k} - 2^k + 1. Unified with `CollisionAnalysis.d`. -/
def kasamiExp (k : ℕ) : ℕ := 2 ^ (2 * k) - 2 ^ k + 1

theorem kasamiExp_eq_d (k : ℕ) : kasamiExp k = CollisionAnalysis.d k := rfl

end KasamiAPN
