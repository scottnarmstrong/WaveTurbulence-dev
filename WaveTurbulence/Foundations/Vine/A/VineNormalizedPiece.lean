/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.RedSplicePiece
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedRedSpliceGap
/-! Exact R83 successor of the producer's Stage 1 data constructor.
Source: pinned/r83-RedSplicePiece.lean, SHA in COPIED-SHA256SUMS.
Only the approved collection and gap choices use the successor namespace. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA.NormalizedSplice
open RedSplice LGSpine Reg.Skeleton
variable {R : ℕ}

/-- **The Stage 1 piece of the original layered garden `LG` and the prescription `σ`.** -/
noncomputable def stage1PieceOf (d : ℕ) {S : Garden (2 * R)} {D : ReconstructionData S}
    (hS : S.IsPlain) (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ : Prescription S)
    (Mk : Set (Stage1.CLVine S) := ∅) : Stage1PieceD d R where
  Gsb := (stSt S σ Mk).G
  Cs := collectionChoices S σ Mk
  ladders := ladderDataOf (stSt S σ Mk).G
  layer := (stSt S σ Mk).layer (RegRed.coreLayer LG D hS hd)
  gapSpecification := gapSpecificationMk S σ Mk
  gsk := gskOf (gregOf D hS LG) S σ (RegRed.coreLayer LG D hS hd) Mk
  bsk := bskOf S σ Mk


end WaveTurbulence.VineA.NormalizedSplice
