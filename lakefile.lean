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
  `WaveTurbulence.Frozen.Theorems.LayergardenFlower, `WaveTurbulence.Provider.LayergardenFlower,
  `WaveTurbulence.Frozen.Theorems.LayergardenFlowerV2, `WaveTurbulence.Provider.LayergardenFlowerV2
]

/-- The formalization of Deng–Hani, *Long time justification of wave turbulence theory*
(arXiv:2311.10082v2). -/
@[default_target]
lean_lib «WaveTurbulence» where
  roots := #[`WaveTurbulence]
  globs := #[.one `WaveTurbulence] ++ quarantinedModules.map .one
  leanOptions := projectLeanOptions

/-- VINEPARAM certificate catalogue (D12). Main-library modules import it, and its whole catalogue (both roots
included) is in the main library's import closure, so `lake build` builds it with the main library. -/
lean_lib «WaveTurbulenceVineParam» where
  roots := #[`WaveTurbulenceVineParam.VineParamMain, `WaveTurbulenceVineParam.VineParamGrouped]
  globs := #[.submodules `WaveTurbulenceVineParam]
  leanOptions := projectLeanOptions

/-- Mathlib-only statement of Theorem 1.1, with one intentional `sorry` (the comparator challenge). -/
@[default_target]
lean_lib «WaveTurbulenceChallenge» where
  roots := #[`WaveTurbulenceChallenge]

/-- The comparator challenge's statement, proved from the library. -/
@[default_target]
lean_lib «WaveTurbulenceSolution» where
  roots := #[`WaveTurbulenceSolution]
