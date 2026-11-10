/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.DescendantClocks
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeSigns

/-! # Literal incoming parent clocks on the actual native regular pieces -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

def parentClockWith {w : ℕ} {tree : Fin w → TTree} (top : Fin w → ℝ)
    (τ : GBranch tree → ℝ) (a : GNode tree) : ℝ :=
  match nodeToSlot a with
  | .inl j => top j
  | .inr (b,_) => τ b

theorem parentClockWith_root {w : ℕ} (tree : Fin w → TTree) (top : Fin w → ℝ)
    (τ : GBranch tree → ℝ) (j : Fin w) : parentClockWith top τ (GNode.root tree j) = top j := rfl

theorem parentClockWith_child {w : ℕ} {tree : Fin w → TTree} (top : Fin w → ℝ)
    (τ : GBranch tree → ℝ) (b : GBranch tree) (i : Fin 3) :
    parentClockWith top τ (b.child i) = τ b := by
  rw [parentClockWith,nodeToSlot_child]

noncomputable def nativeChainClock {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (τ : GBranch (D.forest hS) → ℝ) (b : GBranch S.tree) :
    GBranch (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree → ℝ :=
  fun q => τ (chainContextBranch D hS b ⟨q.1.2,q.2⟩)

end WaveTurbulence.RegRed
