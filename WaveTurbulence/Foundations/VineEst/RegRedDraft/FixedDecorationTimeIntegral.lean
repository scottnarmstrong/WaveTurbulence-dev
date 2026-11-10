/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.KernelIntegrandFactorization

/-! # Actual time integration of a fixed full decoration in native coordinates -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton MeasureTheory

theorem sourceNativeTimeSplit_symm_clocks {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (τ : GBranch S.tree → ℝ) (t : (s : ReplacementSlot S) → NativeTimeBlock D s) :
    (nativeCoreClock D hS ((sourceNativeTimeSplit D hS).symm (τ,t)),
      nativeTimeRestriction D hS ((sourceNativeTimeSplit D hS).symm (τ,t))) = (τ,t) :=
  (sourceNativeTimeSplit_apply D hS _).symm.trans ((sourceNativeTimeSplit D hS).apply_symm_apply (τ,t))

end WaveTurbulence.RegRed
