/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineGapProfile
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedPiece
/-! Complete kernel-relevant A4 data with the actual successor gap product. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Stage1 RedSplice LFTwist LGSpine
variable {w R p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}

/-- A4 data retain the whole gap functional, with the exact garden, layer, hinges and counts. -/
structure PieceProfile (w : ℕ) where
  gap : GapProfile w
  layer : GBranch gap.garden.tree → ℕ
  hinges : Finset (GBranch gap.garden.tree)
  gsk : ℕ
  bsk : ℕ

/-- B1b-3 (Mk-general form of `familyPieceProfile`): the piece fields at the marking `Mk`. -/
noncomputable def familyPieceProfileMk (A : FamilyReconstruction (2 * R) ι) (σ : Prescription A.skeleton)
    (Mk : Set (CLVine A.skeleton)) : PieceProfile (2 * R) where
  gap := gapProfileMk A.skeleton σ Mk
  layer := (NormalizedSplice.stage1PieceOf 0 A.plain A.layered A.decodes σ Mk).layer
  hinges := (NormalizedSplice.stage1PieceOf 0 A.plain A.layered A.decodes σ Mk).Cs.hinges
  gsk := (NormalizedSplice.stage1PieceOf 0 A.plain A.layered A.decodes σ Mk).gsk
  bsk := (NormalizedSplice.stage1PieceOf 0 A.plain A.layered A.decodes σ Mk).bsk

/-- Extract exactly the independently constructed successor piece fields. -/
noncomputable def familyPieceProfile (A : FamilyReconstruction (2 * R) ι) (σ : Prescription A.skeleton) :
    PieceProfile (2 * R) where
  gap := gapProfile A.skeleton σ
  layer := (NormalizedSplice.stage1PieceOf 0 A.plain A.layered A.decodes σ).layer
  hinges := (NormalizedSplice.stage1PieceOf 0 A.plain A.layered A.decodes σ).Cs.hinges
  gsk := (NormalizedSplice.stage1PieceOf 0 A.plain A.layered A.decodes σ).gsk
  bsk := (NormalizedSplice.stage1PieceOf 0 A.plain A.layered A.decodes σ).bsk

end WaveTurbulence.VineA
