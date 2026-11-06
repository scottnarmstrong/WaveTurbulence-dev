/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamNormalizedCertificate.J1IV015
public import WaveTurbulenceVineParam.VineParamNormalizedBaseSupport
import Mathlib.Tactic

/-! # Exact source orientation and all-cap support for IV, profile 15, joint 1 -/

public section
namespace WaveTurbulence.Vine.Param.Normalized.J1IV015

/-- The source template and every fixed physical difference retain the
geometric cap support required for arbitrary insertion. -/
theorem baseSupport : NormalizedBaseSupport (⟨15,by decide⟩ : Fin (baseProfileCount .IV)) certificate := {
  shape_eq := rfl
  ends_profile := ends_profile
  underlying_template := by decide
  forward_counts := by decide
  joints_eq := by decide
  pair_uniform := by decide
  core_uniform := by intro hn; cases hn; decide
  difference_support := by decide
}

end WaveTurbulence.Vine.Param.Normalized.J1IV015
