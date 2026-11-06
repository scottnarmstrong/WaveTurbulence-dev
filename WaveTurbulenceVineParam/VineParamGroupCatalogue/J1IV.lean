/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1IV000
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1IV001
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1IV002
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1IV003
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1IV004
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1IV005
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1IV006
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1IV007
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1IV008
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1IV009
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1IV010
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1IV011
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1IV012
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1IV013
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1IV014
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1IV015
public import WaveTurbulenceVineParam.VineParamGroupCert
import Mathlib.Tactic

/-! # Group-checked source-supported normalized catalogue for J1IV -/

public section
namespace WaveTurbulence.Vine.Param.Normalized

/-- Every allowed source orientation has a checked finite certificate
with the prescribed included joint. -/
theorem catalogue_groups_J1IV (p : Fin (baseProfileCount .IV)) :
    ∃ C : NormalizedVineCertificate .IV, NormalizedBaseSupport p C ∧
      C.matrix.a.1=0 ∧ C.matrix.b.1=1 ∧ C.GroupsOK := by
  fin_cases p
  · exact ⟨J1IV000.certificate,J1IV000.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1IV001.certificate,J1IV001.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1IV002.certificate,J1IV002.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1IV003.certificate,J1IV003.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1IV004.certificate,J1IV004.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1IV005.certificate,J1IV005.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1IV006.certificate,J1IV006.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1IV007.certificate,J1IV007.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1IV008.certificate,J1IV008.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1IV009.certificate,J1IV009.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1IV010.certificate,J1IV010.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1IV011.certificate,J1IV011.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1IV012.certificate,J1IV012.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1IV013.certificate,J1IV013.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1IV014.certificate,J1IV014.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1IV015.certificate,J1IV015.baseSupport,rfl,rfl,by decide +kernel⟩

end WaveTurbulence.Vine.Param.Normalized
