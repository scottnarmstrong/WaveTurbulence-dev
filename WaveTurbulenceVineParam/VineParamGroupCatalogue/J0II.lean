/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0II000
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0II001
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0II002
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0II003
public import WaveTurbulenceVineParam.VineParamGroupCert
import Mathlib.Tactic

/-! # Group-checked source-supported normalized catalogue for J0II -/

public section
namespace WaveTurbulence.Vine.Param.Normalized

/-- Every allowed source orientation has a checked finite certificate
with the prescribed included joint. -/
theorem catalogue_groups_J0II (p : Fin (baseProfileCount .II)) :
    ∃ C : NormalizedVineCertificate .II, NormalizedBaseSupport p C ∧
      C.matrix.a.1=1 ∧ C.matrix.b.1=0 ∧ C.GroupsOK := by
  fin_cases p
  · exact ⟨J0II000.certificate,J0II000.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0II001.certificate,J0II001.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0II002.certificate,J0II002.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0II003.certificate,J0II003.baseSupport,rfl,rfl,by decide +kernel⟩

end WaveTurbulence.Vine.Param.Normalized
