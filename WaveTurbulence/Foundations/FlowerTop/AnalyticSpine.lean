/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import WaveTurbulence.Foundations.FlowerTop.MainLeaf
public import WaveTurbulence.Foundations.FlowerTop.MomentPrefix

/-! Close the native leafwise inputs and supply P7's couple clause over only the named LG producer inputs. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerTop

/-- No leafwise premise remains in the five-field spine constructor. -/
theorem analyticSpine_of_inputs (h5 : P5Input) (hS : Stage1STInput) : FlowerSpineInputsV3 :=
  flowerSpineInputsV3_of_inputs h5 hS leafCoherentInput leafDecayInput

/-- The frozen couple half over the remaining Stage 1/coarse/ladder/count inputs. -/
theorem couple_clause_moment_of_inputs (h5 : P5Input) (hS : Stage1STInput)
    (hcount : LGSpine.FinalCountGateHalf) :
    WTPrefixP (fun _ P => 1 / 2 < P.γ → CoupleClauseAt P) :=
  couple_clause_moment_prefix (analyticSpine_of_inputs h5 hS) hcount

end WaveTurbulence.FlowerTop
