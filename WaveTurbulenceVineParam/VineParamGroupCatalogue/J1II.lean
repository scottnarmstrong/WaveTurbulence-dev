/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1II000
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1II001
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1II002
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1II003
public import WaveTurbulenceVineParam.VineParamGroupCert
import Mathlib.Tactic

/-! # Group-checked source-supported normalized catalogue for J1II -/

public section
namespace WaveTurbulence.Vine.Param.Normalized

/-- Every allowed source orientation has a checked finite certificate
with the prescribed included joint. -/
theorem catalogue_groups_J1II (p : Fin (baseProfileCount .II)) :
    ∃ C : NormalizedVineCertificate .II, NormalizedBaseSupport p C ∧
      C.matrix.a.1=0 ∧ C.matrix.b.1=1 ∧ C.GroupsOK := by
  fin_cases p
  · exact ⟨J1II000.certificate,J1II000.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1II001.certificate,J1II001.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1II002.certificate,J1II002.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1II003.certificate,J1II003.baseSupport,rfl,rfl,by decide +kernel⟩

end WaveTurbulence.Vine.Param.Normalized
