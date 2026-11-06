/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII000
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII001
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII002
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII003
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII004
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII005
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII006
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII007
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII008
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII009
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII010
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII011
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII012
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII013
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII014
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII015
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII016
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII017
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII018
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII019
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII020
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII021
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII022
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII023
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII024
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII025
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII026
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII027
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII028
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII029
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII030
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII031
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII032
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII033
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII034
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII035
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII036
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII037
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII038
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII039
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII040
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII041
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII042
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII043
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII044
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII045
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII046
public import WaveTurbulenceVineParam.VineParamNormalizedSupport.J0VII047
public import WaveTurbulenceVineParam.VineParamGroupCert
import Mathlib.Tactic

/-! # Group-checked source-supported normalized catalogue for J0VII -/

public section
namespace WaveTurbulence.Vine.Param.Normalized

/-- Every allowed source orientation has a checked finite certificate
with the prescribed included joint. -/
theorem catalogue_groups_J0VII (p : Fin (baseProfileCount .VII)) :
    ∃ C : NormalizedVineCertificate .VII, NormalizedBaseSupport p C ∧
      C.matrix.a.1=1 ∧ C.matrix.b.1=0 ∧ C.GroupsOK := by
  fin_cases p
  · exact ⟨J0VII000.certificate,J0VII000.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII001.certificate,J0VII001.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII002.certificate,J0VII002.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII003.certificate,J0VII003.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII004.certificate,J0VII004.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII005.certificate,J0VII005.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII006.certificate,J0VII006.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII007.certificate,J0VII007.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII008.certificate,J0VII008.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII009.certificate,J0VII009.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII010.certificate,J0VII010.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII011.certificate,J0VII011.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII012.certificate,J0VII012.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII013.certificate,J0VII013.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII014.certificate,J0VII014.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII015.certificate,J0VII015.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII016.certificate,J0VII016.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII017.certificate,J0VII017.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII018.certificate,J0VII018.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII019.certificate,J0VII019.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII020.certificate,J0VII020.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII021.certificate,J0VII021.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII022.certificate,J0VII022.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII023.certificate,J0VII023.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII024.certificate,J0VII024.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII025.certificate,J0VII025.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII026.certificate,J0VII026.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII027.certificate,J0VII027.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII028.certificate,J0VII028.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII029.certificate,J0VII029.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII030.certificate,J0VII030.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII031.certificate,J0VII031.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII032.certificate,J0VII032.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII033.certificate,J0VII033.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII034.certificate,J0VII034.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII035.certificate,J0VII035.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII036.certificate,J0VII036.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII037.certificate,J0VII037.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII038.certificate,J0VII038.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII039.certificate,J0VII039.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII040.certificate,J0VII040.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII041.certificate,J0VII041.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII042.certificate,J0VII042.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII043.certificate,J0VII043.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII044.certificate,J0VII044.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII045.certificate,J0VII045.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII046.certificate,J0VII046.baseSupport,rfl,rfl,by decide +kernel⟩
  · exact ⟨J0VII047.certificate,J0VII047.baseSupport,rfl,rfl,by decide +kernel⟩

end WaveTurbulence.Vine.Param.Normalized
