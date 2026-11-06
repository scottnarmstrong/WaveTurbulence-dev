/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII000
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII001
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII002
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII003
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII004
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII005
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII006
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII007
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII008
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII009
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII010
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII011
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII012
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII013
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII014
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII015
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII016
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII017
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII018
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII019
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII020
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII021
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII022
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII023
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII024
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII025
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII026
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII027
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII028
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII029
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII030
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII031
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII032
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII033
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII034
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII035
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII036
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII037
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII038
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII039
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII040
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII041
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII042
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII043
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII044
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII045
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII046
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J1VII047
public import WaveTurbulenceVineParam.VineParamGroupCert
import Mathlib.Tactic

/-! # Group-checked source-supported normalized catalogue for J1VII -/

public section
namespace WaveTurbulence.Vine.Param.Normalized

/-- Every allowed source orientation has a checked finite certificate
with the prescribed included joint. -/
theorem catalogue_groups_J1VII (p : Fin (baseProfileCount .VII)) :
    ∃ C : NormalizedVineCertificate .VII, NormalizedBaseSupport p C ∧
      C.matrix.a.1=0 ∧ C.matrix.b.1=1 ∧ C.GroupsOK := by
  fin_cases p
  · exact ⟨J1VII000.certificate,J1VII000.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII001.certificate,J1VII001.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII002.certificate,J1VII002.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII003.certificate,J1VII003.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII004.certificate,J1VII004.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII005.certificate,J1VII005.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII006.certificate,J1VII006.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII007.certificate,J1VII007.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII008.certificate,J1VII008.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII009.certificate,J1VII009.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII010.certificate,J1VII010.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII011.certificate,J1VII011.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII012.certificate,J1VII012.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII013.certificate,J1VII013.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII014.certificate,J1VII014.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII015.certificate,J1VII015.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII016.certificate,J1VII016.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII017.certificate,J1VII017.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII018.certificate,J1VII018.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII019.certificate,J1VII019.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII020.certificate,J1VII020.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII021.certificate,J1VII021.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII022.certificate,J1VII022.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII023.certificate,J1VII023.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII024.certificate,J1VII024.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII025.certificate,J1VII025.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII026.certificate,J1VII026.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII027.certificate,J1VII027.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII028.certificate,J1VII028.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII029.certificate,J1VII029.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII030.certificate,J1VII030.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII031.certificate,J1VII031.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII032.certificate,J1VII032.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII033.certificate,J1VII033.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII034.certificate,J1VII034.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII035.certificate,J1VII035.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII036.certificate,J1VII036.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII037.certificate,J1VII037.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII038.certificate,J1VII038.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII039.certificate,J1VII039.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII040.certificate,J1VII040.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII041.certificate,J1VII041.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII042.certificate,J1VII042.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII043.certificate,J1VII043.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII044.certificate,J1VII044.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII045.certificate,J1VII045.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII046.certificate,J1VII046.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J1VII047.certificate,J1VII047.baseSupport,rfl,rfl,by decide +kernel⟩

end WaveTurbulence.Vine.Param.Normalized
