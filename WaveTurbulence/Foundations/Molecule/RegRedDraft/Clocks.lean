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

theorem lt_top_of_lt_parentClock {w : ℕ} {tree : Fin w → TTree} (top : ℝ)
    (τ : GBranch tree → ℝ) (h : ∀ b, τ b < parentClock top τ b.toNode)
    (b : GBranch tree) : τ b < top := by
  by_cases hb : b.1.2 = []
  · have he : b.toNode = GNode.root tree b.1.1 := Subtype.ext (Prod.ext rfl hb)
    have ht := h b
    rw [he,parentClock_root] at ht
    exact ht
  · have ht := h b
    change τ b < parentClock top τ b.toNode at ht
    rw [parentClock_nonroot top τ b.toNode hb] at ht
    exact ht.trans (lt_top_of_lt_parentClock top τ h (b.toNode.parent hb))
termination_by b.1.2.length
decreasing_by
  change b.1.2.dropLast.length < b.1.2.length
  have hp : b.1.2.length ≠ 0 := fun he => hb (List.length_eq_zero_iff.mp he)
  rw [List.length_dropLast]
  omega

/-- Branch-only domain: the skeleton is pre-layered, so no equal-layer condition
is imposed on its original paired leaves. -/
def coreTimeDomain {w : ℕ} {tree : Fin w → TTree}
    (layer : GBranch tree → ℕ) (top : ℝ) : Set (GBranch tree → ℝ) :=
  {τ | ∀ b, (layer b : ℝ) < τ b ∧ τ b < layer b + 1 ∧ 0 < τ b ∧
    τ b < parentClock top τ b.toNode}

/-- The actual inherited layer of each retained original branching node. -/
noncomputable def coreLayer {w : ℕ} {S : Garden w} (LG : LayeredGarden w)
    (D : Reg.Skeleton.ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS LG.garden)
    (b : GBranch S.tree) : ℕ := LG.layer (D.decodedCoreBranch hS hd b).toNode

noncomputable def skeletonTimeDomain {w : ℕ} {S : Garden w} (LG : LayeredGarden w)
    (D : Reg.Skeleton.ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS LG.garden)
    (top : ℝ) : Set (GBranch S.tree → ℝ) := coreTimeDomain (coreLayer LG D hS hd) top

end WaveTurbulence.RegRed
