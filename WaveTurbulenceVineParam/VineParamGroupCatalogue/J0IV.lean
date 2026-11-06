/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0IV000
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0IV001
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0IV002
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0IV003
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0IV004
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0IV005
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0IV006
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0IV007
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0IV008
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0IV009
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0IV010
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0IV011
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0IV012
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0IV013
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0IV014
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0IV015
public import WaveTurbulenceVineParam.VineParamGroupCert
import Mathlib.Tactic

/-! # Group-checked source-supported normalized catalogue for J0IV -/

public section
namespace WaveTurbulence.Vine.Param.Normalized

/-- Every allowed source orientation has a checked finite certificate
with the prescribed included joint. -/
theorem catalogue_groups_J0IV (p : Fin (baseProfileCount .IV)) :
    ∃ C : NormalizedVineCertificate .IV, NormalizedBaseSupport p C ∧
      C.matrix.a.1=1 ∧ C.matrix.b.1=0 ∧ C.GroupsOK := by
  fin_cases p
  · exact ⟨J0IV000.certificate,J0IV000.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0IV001.certificate,J0IV001.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0IV002.certificate,J0IV002.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0IV003.certificate,J0IV003.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0IV004.certificate,J0IV004.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0IV005.certificate,J0IV005.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0IV006.certificate,J0IV006.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0IV007.certificate,J0IV007.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0IV008.certificate,J0IV008.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0IV009.certificate,J0IV009.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0IV010.certificate,J0IV010.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0IV011.certificate,J0IV011.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0IV012.certificate,J0IV012.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0IV013.certificate,J0IV013.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0IV014.certificate,J0IV014.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0IV015.certificate,J0IV015.baseSupport,rfl,rfl,by decide +kernel⟩

end WaveTurbulence.Vine.Param.Normalized
