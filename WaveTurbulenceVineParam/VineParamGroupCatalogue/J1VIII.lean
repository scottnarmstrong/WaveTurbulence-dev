/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII000
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII001
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII002
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII003
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII004
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII005
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII006
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII007
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII008
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII009
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII010
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII011
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII012
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII013
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII014
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII015
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII016
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII017
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII018
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII019
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII020
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII021
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII022
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII023
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII024
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII025
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII026
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII027
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII028
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII029
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII030
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VIII031
public import WaveTurbulenceVineParam.VineParamGroupCert
import Mathlib.Tactic

/-! # Group-checked source-supported normalized catalogue for J1VIII -/

public section
namespace WaveTurbulence.Vine.Param.Normalized

/-- Every allowed source orientation has a checked finite certificate
with the prescribed included joint. -/
theorem catalogue_groups_J1VIII (p : Fin (baseProfileCount .VIII)) :
    ∃ C : NormalizedVineCertificate .VIII, NormalizedBaseSupport p C ∧
      C.matrix.a.1=0 ∧ C.matrix.b.1=1 ∧ C.GroupsOK := by
  fin_cases p
  · exact ⟨J1VIII000.certificate,J1VIII000.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII001.certificate,J1VIII001.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII002.certificate,J1VIII002.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII003.certificate,J1VIII003.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII004.certificate,J1VIII004.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII005.certificate,J1VIII005.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII006.certificate,J1VIII006.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII007.certificate,J1VIII007.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII008.certificate,J1VIII008.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII009.certificate,J1VIII009.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII010.certificate,J1VIII010.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII011.certificate,J1VIII011.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII012.certificate,J1VIII012.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII013.certificate,J1VIII013.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII014.certificate,J1VIII014.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII015.certificate,J1VIII015.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII016.certificate,J1VIII016.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII017.certificate,J1VIII017.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII018.certificate,J1VIII018.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII019.certificate,J1VIII019.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII020.certificate,J1VIII020.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII021.certificate,J1VIII021.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII022.certificate,J1VIII022.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII023.certificate,J1VIII023.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII024.certificate,J1VIII024.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII025.certificate,J1VIII025.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII026.certificate,J1VIII026.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII027.certificate,J1VIII027.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII028.certificate,J1VIII028.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII029.certificate,J1VIII029.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII030.certificate,J1VIII030.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VIII031.certificate,J1VIII031.baseSupport,rfl,rfl,by decide +kernel⟩

end WaveTurbulence.Vine.Param.Normalized
