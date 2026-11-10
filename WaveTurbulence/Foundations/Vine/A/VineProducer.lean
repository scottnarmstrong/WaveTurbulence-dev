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

/-- Actual kernel data carrying the successor piece's entries evaluate to the common class functional. -/
theorem normalizedPiece_gapIndicator (a : PrescribedPrimeGarden (2 * R))
    (D : SplicedKernelData (a.normalizedPiece d).Gsb d)
    (hD : D.gapSpecification = (a.normalizedPiece d).gapSpecification)
    {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ))
    (z : GenDecoration (a.normalizedPiece d).Gsb d roots 0) :
    splicedGapIndicator (a.normalizedPiece d).Gsb D L γ η base z.1 =
      a.fullProfile.piece.gap.value d L γ η hL base roots z :=
  (NormalizedSplice.gapValue_eq_indicator a.totalSigma D hD L γ η base z.1).symm

end WaveTurbulence.VineA.PrescribedPrimeGarden
