/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.RelativeDecorations

/-! # Skeleton labels are recovered at every actual attachment after native gluing -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

theorem glueRelativeLabels_leaf {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (κ : GNode S.tree → (Fin d → ℤ)) (hκ : IsDecoration S κ)
    (ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s) (ℓ : GLeaf S.tree) :
    glueRelativeLabels D hS κ ρ (attachedNode D hS ℓ.toNode) = κ ℓ.toNode := by
  by_cases hs : nodeSign S.sig ℓ.1 = 1
  · have h := glueRelativeLabels_couple_root D hS κ ρ (pairOfLeaf S hS ℓ) 0
    change glueRelativeLabels D hS κ ρ
      (attachedNode D hS ((pairOfLeaf S hS ℓ).firstLeaf hS).toNode) =
        κ ((pairOfLeaf S hS ℓ).firstLeaf hS).toNode at h
    have he := (pairOfLeaf_sides_pos S hS ℓ hs).1
    rw [he] at h
    exact h
  · have h := glueRelativeLabels_couple_root D hS κ ρ (pairOfLeaf S hS ℓ) 1
    change glueRelativeLabels D hS κ ρ
      (attachedNode D hS ((pairOfLeaf S hS ℓ).secondLeaf hS).toNode) =
        κ ((pairOfLeaf S hS ℓ).firstLeaf hS).toNode at h
    obtain ⟨h₁,h₂⟩ := pairOfLeaf_sides_neg S hS ℓ hs
    rw [h₁,h₂] at h
    exact h.trans (hκ.2 ℓ).symm

theorem glueRelativeLabels_attached {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (κ : GNode S.tree → (Fin d → ℤ)) (hκ : IsDecoration S κ)
    (ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s) (a : GNode S.tree) :
    glueRelativeLabels D hS κ ρ (attachedNode D hS a) = κ a := by
  rcases (TTree.mem_nodes_iff _ _).mp a.2 with hl | hb
  · exact glueRelativeLabels_leaf D hS κ hκ ρ ⟨a.1,hl⟩
  · exact glueRelativeLabels_chain_root D hS κ ρ ⟨a.1,hb⟩

end WaveTurbulence.RegRed
