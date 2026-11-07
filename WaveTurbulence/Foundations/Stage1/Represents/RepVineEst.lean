/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LayerStatement
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Canon
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Statement

/-!
# S2 REPRESENTS: the VINEEST named input (V5, rulings R43, R46, R47-FINAL, R54, R57)

The single vine-estimate input of S2 is V5's `VineEstCanonLayerHalf` (vineest-s3/uni/src/VineEstS5C/P4/Statement.lean,
sha256 05da7d05…, R54 (ii): bad-vine gain `L^{-(η²/2) b}`), made KIND-GENERIC as ruled in R57 (finding F-KIND): V5's
`CanonReps`/`canonFinset` hardwire `Reach p true` (garden twist class), which for couples (`w = 2`,
`CanonicalObject p false`) is the singleton class.  The kind-generic form sums over `canonFinsetK p kind`, with the
premise `CanonicalObject p kind (layeredReconstruction RD hG layer hLayer)`.

DEVIATION (recorded in HANDOFF): the position of the `kind` binder and of the canonicity premise is S2's choice; V5's
final kind-generic text (V5-KIND pass) replaces this transcription at re-pin.  For `kind = true` the class is V5's
literal `canonFinset` (`canonFinsetK_true`, `rfl`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C VineParamContract TTree
open scoped ENNReal

variable {w : ℕ} {ι : Type*} [Fintype ι]

/-! Deviation (batch 4b-2): the S2 transcriptions `CanonRepsK`, `canonFinsetK`, `canonFinsetK_true` and
`VineEstCanonLayerHalfK` were text-identical to the declarations of main's V5 statement layer; they are reused as aliases
of `VineEstS4.CanonRepsK`, `VineEstS4.canonFinsetK`, `VineEstS4.canonFinsetK_true` and
`VineEstS5C.VineEstCanonLayerHalfK`. -/
export WaveTurbulence.VineEstS4 (CanonRepsK canonFinsetK canonFinsetK_true)
export WaveTurbulence.VineEstS5C (VineEstCanonLayerHalfK)

end WaveTurbulence.Represents
