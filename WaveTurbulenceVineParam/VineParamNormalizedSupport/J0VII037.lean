/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamNormalizedCertificate.J0VII037
public import WaveTurbulenceVineParam.VineParamNormalizedBaseSupport
import Mathlib.Tactic

/-! # Exact source orientation and all-cap support for VII, profile 37, joint 0 -/

public section
namespace WaveTurbulence.Vine.Param.Normalized.J0VII037

/-- The source template and every fixed physical difference retain the
geometric cap support required for arbitrary insertion. -/
theorem baseSupport : NormalizedBaseSupport (⟨37,by decide⟩ : Fin (baseProfileCount .VII)) certificate := {
  shape_eq := rfl
  ends_profile := ends_profile
  underlying_template := by decide
  forward_counts := by decide
  joints_eq := by decide
  pair_uniform := by decide
  core_uniform := by intro hn; cases hn; decide
  difference_support := by decide
}

end WaveTurbulence.Vine.Param.Normalized.J0VII037
