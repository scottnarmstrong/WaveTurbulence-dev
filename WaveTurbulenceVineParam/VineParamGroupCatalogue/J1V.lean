/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1V000
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1V001
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1V002
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1V003
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1V004
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1V005
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1V006
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1V007
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1V008
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1V009
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1V010
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1V011
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1V012
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1V013
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1V014
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1V015
public import WaveTurbulenceVineParam.VineParamGroupCert
import Mathlib.Tactic

/-! # Group-checked source-supported normalized catalogue for J1V -/

public section
namespace WaveTurbulence.Vine.Param.Normalized

/-- Every allowed source orientation has a checked finite certificate
with the prescribed included joint. -/
theorem catalogue_groups_J1V (p : Fin (baseProfileCount .V)) :
    ∃ C : NormalizedVineCertificate .V, NormalizedBaseSupport p C ∧
      C.matrix.a.1=0 ∧ C.matrix.b.1=1 ∧ C.GroupsOK := by
  fin_cases p
  · exact ⟨J1V000.certificate,J1V000.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1V001.certificate,J1V001.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1V002.certificate,J1V002.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1V003.certificate,J1V003.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1V004.certificate,J1V004.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1V005.certificate,J1V005.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1V006.certificate,J1V006.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1V007.certificate,J1V007.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1V008.certificate,J1V008.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1V009.certificate,J1V009.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1V010.certificate,J1V010.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1V011.certificate,J1V011.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1V012.certificate,J1V012.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1V013.certificate,J1V013.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1V014.certificate,J1V014.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1V015.certificate,J1V015.baseSupport,rfl,rfl,by decide +kernel⟩

end WaveTurbulence.Vine.Param.Normalized
