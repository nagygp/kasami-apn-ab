import Lake

open Lake DSL

package «WalshAB» where
  srcDir := "."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

@[default_target]
lean_lib AlmostBent where
  roots := #[
    `AlmostBent.Defs,
    `AlmostBent.CharTwoBasics,
    `AlmostBent.CrossForm,
    `AlmostBent.QuadraticDivisibility,
    `AlmostBent.WalshDiv,
    `AlmostBent.WalshLayers,
    `AlmostBent.KasamiAB
  ]
