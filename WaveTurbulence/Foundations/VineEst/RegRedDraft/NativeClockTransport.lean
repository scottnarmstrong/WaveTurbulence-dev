/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.PairedTreeLowerClock
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.RelativeDecorations

/-! # Original skeleton parent clocks are the exterior clocks of native kernels -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

noncomputable def nativeCoreClock {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (τ : GBranch (D.forest hS) → ℝ) : GBranch S.tree → ℝ :=
  fun b => τ (D.coreBranch hS b)

noncomputable def nativeCoupleClock {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (τ : GBranch (D.forest hS) → ℝ) (p : SourcePair S) :
    GBranch (nativeCoupleGarden D hS p).tree → ℝ := fun q => τ (coupleContextBranch D hS p q)

noncomputable def nativeCoupleUpper {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (top : ℝ) (τ : GBranch S.tree → ℝ) (p : SourcePair S) : Fin 2 → ℝ :=
  ![parentClock top τ (p.firstLeaf hS).toNode,parentClock top τ (p.secondLeaf hS).toNode]

end WaveTurbulence.RegRed
