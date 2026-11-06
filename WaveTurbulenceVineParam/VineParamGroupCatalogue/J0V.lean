/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0V000
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0V001
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0V002
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0V003
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0V004
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0V005
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0V006
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0V007
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0V008
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0V009
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0V010
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0V011
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0V012
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0V013
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0V014
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0V015
public import WaveTurbulenceVineParam.VineParamGroupCert
import Mathlib.Tactic

/-! # Group-checked source-supported normalized catalogue for J0V -/

public section
namespace WaveTurbulence.Vine.Param.Normalized

/-- Every allowed source orientation has a checked finite certificate
with the prescribed included joint. -/
theorem catalogue_groups_J0V (p : Fin (baseProfileCount .V)) :
    ∃ C : NormalizedVineCertificate .V, NormalizedBaseSupport p C ∧
      C.matrix.a.1=1 ∧ C.matrix.b.1=0 ∧ C.GroupsOK := by
  fin_cases p
  · exact ⟨J0V000.certificate,J0V000.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0V001.certificate,J0V001.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0V002.certificate,J0V002.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0V003.certificate,J0V003.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0V004.certificate,J0V004.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0V005.certificate,J0V005.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0V006.certificate,J0V006.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0V007.certificate,J0V007.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0V008.certificate,J0V008.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0V009.certificate,J0V009.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0V010.certificate,J0V010.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0V011.certificate,J0V011.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0V012.certificate,J0V012.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0V013.certificate,J0V013.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0V014.certificate,J0V014.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0V015.certificate,J0V015.baseSupport,rfl,rfl,by decide +kernel⟩

end WaveTurbulence.Vine.Param.Normalized
