/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamGroupCatalogue.J0I
public import WaveTurbulenceVineParam.VineParamGroupCatalogue.J1I
public import WaveTurbulenceVineParam.VineParamGroupCatalogue.J0II
public import WaveTurbulenceVineParam.VineParamGroupCatalogue.J1II
public import WaveTurbulenceVineParam.VineParamGroupCatalogue.J0III
public import WaveTurbulenceVineParam.VineParamGroupCatalogue.J1III
public import WaveTurbulenceVineParam.VineParamGroupCatalogue.J0IV
public import WaveTurbulenceVineParam.VineParamGroupCatalogue.J1IV
public import WaveTurbulenceVineParam.VineParamGroupCatalogue.J0V
public import WaveTurbulenceVineParam.VineParamGroupCatalogue.J1V
public import WaveTurbulenceVineParam.VineParamGroupCatalogue.J0VI
public import WaveTurbulenceVineParam.VineParamGroupCatalogue.J1VI
public import WaveTurbulenceVineParam.VineParamGroupCatalogue.J0VII
public import WaveTurbulenceVineParam.VineParamGroupCatalogue.J1VII
public import WaveTurbulenceVineParam.VineParamGroupCatalogue.J0VIII
public import WaveTurbulenceVineParam.VineParamGroupCatalogue.J1VIII

import Mathlib.Tactic

/-! # Group-checked normalized base catalogue for every vine type -/

public section
namespace WaveTurbulence.Vine.Param

/-- All normalized source orientations and both included-joint choices have
concrete checked full certificates, including the m=1 type-II endpoint. -/
theorem exists_normalized_base_certificate_groups (X : VineType) (joint : Fin 2)
    (p : Fin (baseProfileCount X)) :
    ∃ C : NormalizedVineCertificate X,NormalizedBaseSupport p C ∧
      C.matrix.a.1=1-joint.1 ∧ C.matrix.b.1=joint.1 ∧ C.GroupsOK := by
  cases X <;> fin_cases joint
  · exact Normalized.catalogue_groups_J0I p
  · exact Normalized.catalogue_groups_J1I p
  · exact Normalized.catalogue_groups_J0II p
  · exact Normalized.catalogue_groups_J1II p
  · exact Normalized.catalogue_groups_J0III p
  · exact Normalized.catalogue_groups_J1III p
  · exact Normalized.catalogue_groups_J0IV p
  · exact Normalized.catalogue_groups_J1IV p
  · exact Normalized.catalogue_groups_J0V p
  · exact Normalized.catalogue_groups_J1V p
  · exact Normalized.catalogue_groups_J0VI p
  · exact Normalized.catalogue_groups_J1VI p
  · exact Normalized.catalogue_groups_J0VII p
  · exact Normalized.catalogue_groups_J1VII p
  · exact Normalized.catalogue_groups_J0VIII p
  · exact Normalized.catalogue_groups_J1VIII p

end WaveTurbulence.Vine.Param
