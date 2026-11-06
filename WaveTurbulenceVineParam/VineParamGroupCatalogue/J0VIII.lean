/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII000
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII001
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII002
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII003
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII004
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII005
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII006
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII007
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII008
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII009
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII010
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII011
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII012
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII013
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII014
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII015
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII016
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII017
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII018
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII019
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII020
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII021
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII022
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII023
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII024
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII025
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII026
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII027
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII028
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII029
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII030
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VIII031
public import WaveTurbulenceVineParam.VineParamGroupCert
import Mathlib.Tactic

/-! # Group-checked source-supported normalized catalogue for J0VIII -/

public section
namespace WaveTurbulence.Vine.Param.Normalized

/-- Every allowed source orientation has a checked finite certificate
with the prescribed included joint. -/
theorem catalogue_groups_J0VIII (p : Fin (baseProfileCount .VIII)) :
    ∃ C : NormalizedVineCertificate .VIII, NormalizedBaseSupport p C ∧
      C.matrix.a.1=1 ∧ C.matrix.b.1=0 ∧ C.GroupsOK := by
  fin_cases p
  · exact ⟨J0VIII000.certificate,J0VIII000.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII001.certificate,J0VIII001.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII002.certificate,J0VIII002.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII003.certificate,J0VIII003.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII004.certificate,J0VIII004.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII005.certificate,J0VIII005.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII006.certificate,J0VIII006.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII007.certificate,J0VIII007.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII008.certificate,J0VIII008.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII009.certificate,J0VIII009.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII010.certificate,J0VIII010.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII011.certificate,J0VIII011.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII012.certificate,J0VIII012.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII013.certificate,J0VIII013.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII014.certificate,J0VIII014.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII015.certificate,J0VIII015.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII016.certificate,J0VIII016.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII017.certificate,J0VIII017.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII018.certificate,J0VIII018.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII019.certificate,J0VIII019.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII020.certificate,J0VIII020.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII021.certificate,J0VIII021.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII022.certificate,J0VIII022.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII023.certificate,J0VIII023.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII024.certificate,J0VIII024.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII025.certificate,J0VIII025.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII026.certificate,J0VIII026.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII027.certificate,J0VIII027.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII028.certificate,J0VIII028.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII029.certificate,J0VIII029.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII030.certificate,J0VIII030.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VIII031.certificate,J0VIII031.baseSupport,rfl,rfl,by decide +kernel⟩

end WaveTurbulence.Vine.Param.Normalized
