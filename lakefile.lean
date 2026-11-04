import Lake

open Lake DSL

package «waveTurbulence» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

private def projectLeanOptions : Array LeanOption := #[
  ⟨`autoImplicit, false⟩,
  ⟨`relaxedAutoImplicit, false⟩,
  ⟨`linter.unusedVariables, true⟩,
  ⟨`linter.unusedSectionVars, true⟩,
  ⟨`linter.deprecated, true⟩
]

/-- The frozen theorem anchors in state `DRAFT_SORRY` and their provider modules. The frozen-anchor
quarantine forbids every other module, the root included, from importing them, so the library
builds them as extra globs beside its root. -/
private def quarantinedModules : Array Lean.Name := #[
  `WaveTurbulence.Frozen.Theorems.Main, `WaveTurbulence.Provider.Main,
  `WaveTurbulence.Frozen.Theorems.CanonicalCharacterization, `WaveTurbulence.Provider.CanonicalCharacterization,
  `WaveTurbulence.Frozen.Theorems.Fixedpoint, `WaveTurbulence.Provider.Fixedpoint,
  `WaveTurbulence.Frozen.Theorems.Layergarden, `WaveTurbulence.Provider.Layergarden,
  `WaveTurbulence.Frozen.Theorems.LayergardenFlower, `WaveTurbulence.Provider.LayergardenFlower,
  `WaveTurbulence.Frozen.Theorems.Propansatz, `WaveTurbulence.Provider.Propansatz,
  `WaveTurbulence.Frozen.Theorems.QuadExpSum2, `WaveTurbulence.Provider.QuadExpSum2,
  `WaveTurbulence.Frozen.Theorems.QuadExpSum3, `WaveTurbulence.Provider.QuadExpSum3,
  `WaveTurbulence.Frozen.Theorems.Sumint, `WaveTurbulence.Provider.Sumint,
  `WaveTurbulence.Frozen.Theorems.WkeTaylor, `WaveTurbulence.Provider.WkeTaylor
]

/-- The formalization of Deng–Hani, *Long time justification of wave turbulence theory*
(arXiv:2311.10082v2). -/
@[default_target]
lean_lib «WaveTurbulence» where
  roots := #[`WaveTurbulence]
  globs := #[.one `WaveTurbulence] ++ quarantinedModules.map .one
  leanOptions := projectLeanOptions
