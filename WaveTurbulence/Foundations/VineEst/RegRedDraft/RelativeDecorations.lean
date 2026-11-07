/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeNodeEquiv
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CollapsedDecorations
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.DecorationShift

/-! # Root-zero decoration fibers of the actual native replacements -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

noncomputable def nativeCoupleGarden {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (p : SourcePair S) : Garden 2 :=
  Comb.RootedSubforest.inducedGarden (G := D.garden hS) (nativeCoupleForest D hS p)
    (nativeCoupleForest_closed D hS p)

def NativeRelativeDecoration {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (d : ℕ) : ReplacementSlot S → Type
  | .inl p => GenDecoration (nativeCoupleGarden D hS p) d (fun _ => 0) 0
  | .inr b => GenDecoration (decodedTree (D.tree b) (nodeSign S.sig b.1)) d (fun _ => 0) 0

noncomputable def relativeNativeLabels {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (κ : GNode S.tree → (Fin d → ℤ))
    (ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s) :
    (s : ReplacementSlot S) → NativeNode D s → (Fin d → ℤ)
  | .inl p,a => (ρ (.inl p)).1 a + κ (p.firstLeaf hS).toNode
  | .inr b,a => (ρ (.inr b)).1 a + κ b.toNode

noncomputable def glueRelativeLabels {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (κ : GNode S.tree → (Fin d → ℤ))
    (ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s) :
    GNode (D.forest hS) → (Fin d → ℤ) :=
  glueNativeLabels D hS (relativeNativeLabels D hS κ ρ)

theorem glueRelativeLabels_couple_root {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (κ : GNode S.tree → (Fin d → ℤ))
    (ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s)
    (p : SourcePair S) (j : Fin 2) :
    glueRelativeLabels D hS κ ρ ((nativeCoupleForest D hS p).root j) = κ (p.firstLeaf hS).toNode := by
  have h := glueNativeLabels_at D hS (relativeNativeLabels D hS κ ρ) (.inl p)
    (GNode.root (decodedCouple (D.couple p)).tree j)
  have hr := subforest_node_root (nativeCoupleForest D hS p) j
  change glueRelativeLabels D hS κ ρ ((nativeCoupleForest D hS p).nodeEmbedding _) =
    (ρ (.inl p)).1 (GNode.root _ j) + κ (p.firstLeaf hS).toNode at h
  have hz := (ρ (.inl p)).2.2.1 j
  exact (congrArg (glueRelativeLabels D hS κ ρ) hr).symm.trans
    (h.trans (by rw [hz,zero_add]))

theorem glueRelativeLabels_chain_root {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (κ : GNode S.tree → (Fin d → ℤ))
    (ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s) (b : GBranch S.tree) :
    glueRelativeLabels D hS κ ρ (attachedNode D hS b.toNode) = κ b.toNode := by
  have h := glueNativeLabels_at D hS (relativeNativeLabels D hS κ ρ) (.inr b) (GNode.root _ 0)
  change glueRelativeLabels D hS κ ρ (chainContextNode D hS b (GNode.root _ 0)) =
    (ρ (.inr b)).1 (GNode.root _ 0) + κ b.toNode at h
  exact (congrArg (glueRelativeLabels D hS κ ρ) (chainContextNode_root D hS b)).symm.trans
    (h.trans (by rw [(ρ (.inr b)).2.2.1 0,zero_add]))

theorem glueRelativeLabels_core {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (κ : GNode S.tree → (Fin d → ℤ))
    (ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s) (b : GBranch S.tree) :
    glueRelativeLabels D hS κ ρ (D.coreBranch hS b).toNode = κ b.toNode := by
  let ℓ := chainLoneLeaf (D.tree b) (nodeSign S.sig b.1)
  have hz := pairedTree_lone_eq_root (decodedTree_isPairedTree (D.tree b) (nodeSign S.sig b.1))
    (ρ (.inr b)).1 (ρ (.inr b)).2.1 ℓ
    ((decodesTree_lone_iff (decodedTree_decodes _ _) _).mpr rfl)
  have h := glueNativeLabels_at D hS (relativeNativeLabels D hS κ ρ) (.inr b) ℓ.toNode
  change glueRelativeLabels D hS κ ρ (chainContextNode D hS b ℓ.toNode) =
    (ρ (.inr b)).1 ℓ.toNode + κ b.toNode at h
  exact (congrArg (glueRelativeLabels D hS κ ρ) (chainContextNode_lone D hS b)).symm.trans
    (h.trans ((congrArg (fun v => v + κ b.toNode)
      (hz.trans ((ρ (.inr b)).2.2.1 0))).trans (zero_add _)))

end WaveTurbulence.RegRed
