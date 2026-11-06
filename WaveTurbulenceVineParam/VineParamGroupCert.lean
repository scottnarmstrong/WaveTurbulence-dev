/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamGroupSet
public import WaveTurbulenceVineParam.VineParamNormalizedVineCertificate
public import WaveTurbulence.Foundations.Molecule.VineTemplates
import Mathlib.Tactic

/-! # Group agreement of a normalized base certificate with the template groups -/

public section
namespace WaveTurbulence.Vine.Param
open Finset VineParamContract

namespace NormalizedVineCertificate
variable {X : VineType} (C : NormalizedVineCertificate X)

/-- The chart groups of a base certificate, in template labels, are exactly the template groups. -/
@[expose] def GroupsOK : Prop :=
  shapeGroupSet C.shape (fun i => (C.atom i).1.1) = listGroupSet X.template.groups

instance : Decidable C.GroupsOK := by unfold GroupsOK; infer_instance

end NormalizedVineCertificate
end WaveTurbulence.Vine.Param
