/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.FixedDecorationTimeIntegral
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeInputSummability

/-! # Absolute Fubini for the independent native decoration fibers -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton MeasureTheory

theorem glueGenDecoration_injective {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration S d n nfl) : Function.Injective (glueGenDecoration D hS κ) := by
  intro ρ η he
  have h := congrArg (fun k : GenDecoration (D.garden hS) d n nfl => restrictRelativeDecorations D hS k) he
  exact (restrictRelativeDecorations_glue D hS κ ρ).symm.trans
    (h.trans (restrictRelativeDecorations_glue D hS κ η))

end WaveTurbulence.RegRed
