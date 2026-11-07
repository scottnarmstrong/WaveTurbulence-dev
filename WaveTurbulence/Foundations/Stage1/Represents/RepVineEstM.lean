/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVineEst
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ModStatement

/-!
# S2 REPRESENTS: the VINEEST named input after R58 (modulated) and R57 (kind-generic)

V5's `VineEstCanonLayerHalfM` (vineest-s3/uni/src/VineEstS5C/P4/W2/ModStatement.lean, sha256 bd646966…, R54 (ii) with the
modulation `e^{πiλτ_b}` at the lower joint of the unit and the loss `(1 + |λ|)^{6η⁶}`, on V5-CONT's
`Cont.twistedRecenteredModC`, Cont/ModClass.lean sha256 35576abd…), made kind-generic as ruled in R57: the class is
`canonFinsetK p kind`, with the premise `CanonicalObject p kind (layeredReconstruction RD hG layer hLayer)`.
For `kind = true` the class is V5's literal `canonFinset` (`canonFinsetK_true`, `rfl`).
DEVIATION (HANDOFF): the position of the `kind` binder and of the canonicity premise is S2's choice until V5-KIND.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C VineParamContract TTree
open scoped ENNReal

/-! Deviation (batch 4b-2): the S2 transcription of `VineEstCanonLayerHalfMK` was text-identical to V5's
(`VineEstS5C.VineEstCanonLayerHalfMK`, `P4.W2.ModStatement`); it is reused as an alias. -/
export WaveTurbulence.VineEstS5C (VineEstCanonLayerHalfMK)

end WaveTurbulence.Represents
