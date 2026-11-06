/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1III000
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1III001
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1III002
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1III003
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1III004
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1III005
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1III006
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1III007
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1III008
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1III009
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1III010
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1III011
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1III012
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1III013
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1III014
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1III015
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1III016
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1III017
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1III018
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1III019
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1III020
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1III021
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1III022
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1III023
public import WaveTurbulenceVineParam.VineParamGroupCert
import Mathlib.Tactic

/-! # Group-checked source-supported normalized catalogue for J1III -/

public section
namespace WaveTurbulence.Vine.Param.Normalized

/-- Every allowed source orientation has a checked finite certificate
with the prescribed included joint. -/
theorem catalogue_groups_J1III (p : Fin (baseProfileCount .III)) :
    ∃ C : NormalizedVineCertificate .III, NormalizedBaseSupport p C ∧
      C.matrix.a.1=0 ∧ C.matrix.b.1=1 ∧ C.GroupsOK := by
  fin_cases p
  · exact ⟨J1III000.certificate,J1III000.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1III001.certificate,J1III001.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1III002.certificate,J1III002.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1III003.certificate,J1III003.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1III004.certificate,J1III004.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1III005.certificate,J1III005.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1III006.certificate,J1III006.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1III007.certificate,J1III007.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1III008.certificate,J1III008.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1III009.certificate,J1III009.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1III010.certificate,J1III010.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1III011.certificate,J1III011.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1III012.certificate,J1III012.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1III013.certificate,J1III013.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1III014.certificate,J1III014.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1III015.certificate,J1III015.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1III016.certificate,J1III016.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1III017.certificate,J1III017.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1III018.certificate,J1III018.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1III019.certificate,J1III019.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1III020.certificate,J1III020.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1III021.certificate,J1III021.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1III022.certificate,J1III022.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1III023.certificate,J1III023.baseSupport,rfl,rfl,by decide +kernel⟩

end WaveTurbulence.Vine.Param.Normalized
