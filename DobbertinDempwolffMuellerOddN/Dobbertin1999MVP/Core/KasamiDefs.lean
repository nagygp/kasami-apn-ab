import Mathlib

namespace KasamiAPN

/-- A function `f : F → F` is APN (Almost Perfect Nonlinear) if for every nonzero `a`,
any collision `f(x+a)+f(x) = f(y+a)+f(y)` forces `y ∈ {x, x+a}`. -/
def IsAPN {F : Type*} [Field F] [CharP F 2] (f : F → F) : Prop :=
  ∀ (a : F), a ≠ 0 → ∀ (x y : F),
    f (x + a) + f x = f (y + a) + f y → y = x ∨ y = x + a

/-- The Kasami exponent `d = 2^(2k) - 2^k + 1`. -/
def kasamiExp (k : ℕ) : ℕ := 2 ^ (2 * k) - 2 ^ k + 1

end KasamiAPN
