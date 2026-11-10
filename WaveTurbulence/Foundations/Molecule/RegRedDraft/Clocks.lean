/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.NodeSlots
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.DecodedCoreEmbedding

/-! # Parent clocks and the pre-layered skeleton time domain (TARGET redkg) -/

@[expose] public section
namespace WaveTurbulence.RegRed
open TTree Reg.Skeleton

/-- Original source-parent time, read as the exterior top clock at a root. -/
def parentClock {w : ℕ} {tree : Fin w → TTree} (top : ℝ)
    (τ : GBranch tree → ℝ) (a : GNode tree) : ℝ :=
  match nodeToSlot a with
  | .inl _ => top
  | .inr (b,_) => τ b

theorem parentClock_root {w : ℕ} (tree : Fin w → TTree) (top : ℝ)
    (τ : GBranch tree → ℝ) (j : Fin w) : parentClock top τ (GNode.root tree j) = top := by
  rfl

theorem parentClock_child {w : ℕ} {tree : Fin w → TTree} (top : ℝ)
    (τ : GBranch tree → ℝ) (b : GBranch tree) (i : Fin 3) :
    parentClock top τ (b.child i) = τ b := by
  rw [parentClock,nodeToSlot_child]

theorem parentClock_nonroot {w : ℕ} {tree : Fin w → TTree} (top : ℝ)
    (τ : GBranch tree → ℝ) (a : GNode tree) (ha : a.1.2 ≠ []) :
    parentClock top τ a = τ (a.parent ha) := by
  rw [parentClock,nodeToSlot,dite_eq_right ha]

/-- The actual inherited layer of each retained original branching node. -/
noncomputable def coreLayer {w : ℕ} {S : Garden w} (LG : LayeredGarden w)
    (D : Reg.Skeleton.ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS LG.garden)
    (b : GBranch S.tree) : ℕ := LG.layer (D.decodedCoreBranch hS hd b).toNode

end WaveTurbulence.RegRed
