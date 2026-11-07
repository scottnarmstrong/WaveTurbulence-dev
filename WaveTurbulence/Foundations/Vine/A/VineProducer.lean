/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineFullA4
/-! Direct S2 consumer bridges from actual successor pieces to the common A4 functional. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
namespace WaveTurbulence.VineA.PrescribedPrimeGarden
open Stage1 RedSplice LGSpine
variable {R d : ℕ}

/-- The common collection count is the actual producer field in every momentum dimension. -/
theorem normalizedPiece_collection_count (a : PrescribedPrimeGarden (2 * R)) (d : ℕ) :
    (a.normalizedPiece d).Cs.count = a.fullProfile.count := rfl

/-- Ladders are chosen from the literal common spliced garden. -/
theorem plainTau_ladders {p : ℕ} {kind : Bool} {a b : PrescribedPrimeGarden (2 * R)}
    (hσ : b.code = a.code) (h : b.layered ∈ a.outputs (p := p) (kind := kind)) (d : ℕ) :
    HEq (b.normalizedPiece d).ladders (a.normalizedPiece d).ladders := by
  have hg : (b.normalizedPiece d).Gsb = (a.normalizedPiece d).Gsb :=
    congrArg (fun P => P.piece.gap.garden) (plainTau_fullA4 hσ h)
  have key {G H : Garden (2 * R)} (he : G = H) : HEq (ladderDataOf G) (ladderDataOf H) := by
    cases he; rfl
  exact key hg

/-- The actual ladder incoherency field also agrees on every fixed-sigma tau class. -/
theorem plainTau_gsb {p : ℕ} {kind : Bool} {a b : PrescribedPrimeGarden (2 * R)}
    (hσ : b.code = a.code) (h : b.layered ∈ a.outputs (p := p) (kind := kind)) (d : ℕ) :
    (b.normalizedPiece d).gsb = (a.normalizedPiece d).gsb := by
  have he : b.fullProfile = a.fullProfile := plainTau_fullA4 hσ h
  have hi := congrArg (fun P : FullA4Profile (2 * R) =>
    (ladderDataOf P.piece.gap.garden).totalIncoherency P.piece.layer) he
  exact hi

/-- Actual kernel data carrying the successor piece's entries evaluate to the common class functional. -/
theorem normalizedPiece_gapIndicator (a : PrescribedPrimeGarden (2 * R))
    (D : SplicedKernelData (a.normalizedPiece d).Gsb d)
    (hD : D.gapSpecification = (a.normalizedPiece d).gapSpecification)
    {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ))
    (z : GenDecoration (a.normalizedPiece d).Gsb d roots 0) :
    splicedGapIndicator (a.normalizedPiece d).Gsb D L γ η base z.1 =
      a.fullProfile.piece.gap.value d L γ η hL base roots z :=
  (NormalizedSplice.gapValue_eq_indicator a.totalSigma D hD L γ η base z.1).symm

/-- S2's literal Stage1Piece.data has the common complete gap factor for every analytic input. -/
theorem normalizedPiece_data_gapIndicator (P : WTParams) (a : PrescribedPrimeGarden (2 * R))
    (tt : Fin (2 * R) → ℝ) (center : GardenDart (a.normalizedPiece P.d).Gsb → Mom P.d)
    (edge : GardenDart (a.normalizedPiece P.d).Gsb → Mom P.d → ℂ)
    (hinge : (HingeDarts (a.normalizedPiece P.d).Gsb (a.normalizedPiece P.d).Cs.hinges → Mom P.d) → ℂ)
    (freq : GBranch (a.normalizedPiece P.d).Gsb.tree → ℝ)
    (hL : P.L ≠ 0) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (z : GenDecoration (a.normalizedPiece P.d).Gsb P.d roots 0) :
    splicedGapIndicator (a.normalizedPiece P.d).Gsb
      (Stage1Piece.data (P := P) (a.normalizedPiece P.d) tt center edge hinge freq) P.L P.γ P.η base z.1 =
      a.fullProfile.piece.gap.value P.d P.L P.γ P.η hL base roots z :=
  normalizedPiece_gapIndicator a _ rfl hL P.γ P.η base roots z

end WaveTurbulence.VineA.PrescribedPrimeGarden
