/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0I000
public import WaveTurbulenceVineParam.VineParamGroupCert
import Mathlib.Tactic

/-! # Group-checked source-supported normalized catalogue for J0I -/

public section
namespace WaveTurbulence.Vine.Param.Normalized

/-- Every allowed source orientation has a checked finite certificate
with the prescribed included joint. -/
theorem catalogue_groups_J0I (p : Fin (baseProfileCount .I)) :
    ∃ C : NormalizedVineCertificate .I, NormalizedBaseSupport p C ∧
      C.matrix.a.1=1 ∧ C.matrix.b.1=0 ∧ C.GroupsOK := by
  fin_cases p
  · exact ⟨J0I000.certificate,J0I000.baseSupport,rfl,rfl,by decide +kernel⟩

end WaveTurbulence.Vine.Param.Normalized
