/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.GluedAttachmentLabels
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeSigns

/-! # Actual branching conservation after gluing independent native decorations -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

theorem glued_couple_isDecoration {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (κ : GNode S.tree → (Fin d → ℤ))
    (ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s) (p : SourcePair S) :
    IsDecoration (nativeCoupleGarden D hS p)
      (fun a => glueRelativeLabels D hS κ ρ ((nativeCoupleForest D hS p).nodeEmbedding a)) := by
  have he : (fun a : GNode (nativeCoupleGarden D hS p).tree =>
      glueRelativeLabels D hS κ ρ ((nativeCoupleForest D hS p).nodeEmbedding a)) =
      (fun a => (ρ (.inl p)).1 a + κ (p.firstLeaf hS).toNode) :=
    funext (fun a => glueNativeLabels_at D hS (relativeNativeLabels D hS κ ρ) (.inl p) a)
  rw [he]
  exact isDecoration_add _ _ (ρ (.inl p)).2.1 _

theorem glued_chain_isDecoration {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (κ : GNode S.tree → (Fin d → ℤ))
    (ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s) (b : GBranch S.tree) :
    IsDecoration (decodedTree (D.tree b) (nodeSign S.sig b.1))
      (fun a => glueRelativeLabels D hS κ ρ (chainContextNode D hS b a)) := by
  have he : (fun a : GNode (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree =>
      glueRelativeLabels D hS κ ρ (chainContextNode D hS b a)) =
      (fun a => (ρ (.inr b)).1 a + κ b.toNode) :=
    funext (fun a => glueNativeLabels_at D hS (relativeNativeLabels D hS κ ρ) (.inr b) a)
  rw [he]
  exact isDecoration_add _ _ (ρ (.inr b)).2.1 _

/-- Every genuine full branch satisfies conservation after gluing. The three
cases are exhaustive by the proved literal source branch equivalence. -/
theorem glueRelativeLabels_conservation {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (κ : GNode S.tree → (Fin d → ℤ)) (hκ : IsDecoration S κ)
    (ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s)
    (c : GBranch (D.forest hS)) :
    glueRelativeLabels D hS κ ρ c.toNode =
      glueRelativeLabels D hS κ ρ (c.child 0) - glueRelativeLabels D hS κ ρ (c.child 1) +
        glueRelativeLabels D hS κ ρ (c.child 2) := by
  let η := glueRelativeLabels D hS κ ρ
  have hc (b : GBranch S.tree) (i : Fin 3) : η ((D.coreBranch hS b).child i) = κ (b.child i) :=
    (congrArg η (attachedNode_child D hS b i)).symm.trans
      (glueRelativeLabels_attached D hS κ hκ ρ (b.child i))
  obtain ⟨x,rfl⟩ := (sourceBranchEquiv D hS).surjective c
  rcases x with b | (⟨p,q⟩ | ⟨b,q⟩)
  · exact (glueRelativeLabels_core D hS κ ρ b).trans
      ((hκ.1 b).trans (congrArg₂ (· + ·) (congrArg₂ (· - ·) (hc b 0).symm (hc b 1).symm)
        (hc b 2).symm))
  · let E := nativeCoupleForest D hS p
    have h := (glued_couple_isDecoration D hS κ ρ p).1 q
    have h0 := congrArg η (subforest_node_child E q 0)
    have h1 := congrArg η (subforest_node_child E q 1)
    have h2 := congrArg η (subforest_node_child E q 2)
    exact (congrArg η (subforest_branch_node E q)).symm.trans
      (h.trans (congrArg₂ (· + ·) (congrArg₂ (· - ·) h0 h1) h2))
  · let q' := chainBranchEquiv D b q
    have h := (glued_chain_isDecoration D hS κ ρ b).1 q'
    have h0 := congrArg η (chainContextNode_child D hS b q' 0)
    have h1 := congrArg η (chainContextNode_child D hS b q' 1)
    have h2 := congrArg η (chainContextNode_child D hS b q' 2)
    exact h.trans (congrArg₂ (· + ·) (congrArg₂ (· - ·) h0 h1) h2)

end WaveTurbulence.RegRed
