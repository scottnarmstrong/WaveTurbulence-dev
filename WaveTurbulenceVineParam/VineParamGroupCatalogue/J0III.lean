/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0III000
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0III001
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0III002
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0III003
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0III004
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0III005
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0III006
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0III007
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0III008
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0III009
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0III010
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0III011
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0III012
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0III013
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0III014
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0III015
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0III016
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0III017
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0III018
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0III019
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0III020
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0III021
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0III022
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0III023
public import WaveTurbulenceVineParam.VineParamGroupCert
import Mathlib.Tactic

/-! # Group-checked source-supported normalized catalogue for J0III -/

public section
namespace WaveTurbulence.Vine.Param.Normalized

/-- Every allowed source orientation has a checked finite certificate
with the prescribed included joint. -/
theorem catalogue_groups_J0III (p : Fin (baseProfileCount .III)) :
    ∃ C : NormalizedVineCertificate .III, NormalizedBaseSupport p C ∧
      C.matrix.a.1=1 ∧ C.matrix.b.1=0 ∧ C.GroupsOK := by
  fin_cases p
  · exact ⟨J0III000.certificate,J0III000.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0III001.certificate,J0III001.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0III002.certificate,J0III002.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0III003.certificate,J0III003.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0III004.certificate,J0III004.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0III005.certificate,J0III005.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0III006.certificate,J0III006.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0III007.certificate,J0III007.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0III008.certificate,J0III008.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0III009.certificate,J0III009.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0III010.certificate,J0III010.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0III011.certificate,J0III011.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0III012.certificate,J0III012.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0III013.certificate,J0III013.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0III014.certificate,J0III014.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0III015.certificate,J0III015.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0III016.certificate,J0III016.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0III017.certificate,J0III017.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0III018.certificate,J0III018.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0III019.certificate,J0III019.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0III020.certificate,J0III020.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0III021.certificate,J0III021.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0III022.certificate,J0III022.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0III023.certificate,J0III023.baseSupport,rfl,rfl,by decide +kernel⟩

end WaveTurbulence.Vine.Param.Normalized
