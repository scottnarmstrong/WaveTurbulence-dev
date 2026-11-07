/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CenteredDecorations

/-! # Restricting and centering actual full decorations on native regular pieces -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

theorem nativeCouple_roots_value {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (κ : GNode (D.forest hS) → (Fin d → ℤ))
    (hκ : IsDecoration (D.garden hS) κ) (p : SourcePair S) (j : Fin 2) :
    κ ((nativeCoupleForest D hS p).nodeEmbedding (GNode.root _ j)) =
      κ (attachedNode D hS (p.firstLeaf hS).toNode) := by
  have h := congrArg κ (subforest_node_root (nativeCoupleForest D hS p) j)
  fin_cases j
  · exact h
  · exact h.trans (couple_attachment_momentum D hS κ hκ p).symm

theorem nativeChain_roots_value {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (κ : GNode (D.forest hS) → (Fin d → ℤ))
    (b : GBranch S.tree) (j : Fin 1) :
    κ (chainContextNode D hS b (GNode.root _ j)) = κ (attachedNode D hS b.toNode) := by
  fin_cases j
  exact congrArg κ (chainContextNode_root D hS b)

noncomputable def restrictRelativeDecorations {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) :
    (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s
  | .inl p => centerGenDecoration (nativeCoupleGarden D hS p)
      (fun a => κ.1 ((nativeCoupleForest D hS p).nodeEmbedding a))
      (subforest_isDecoration (D.garden hS) (nativeCoupleForest D hS p)
        (nativeCoupleForest_closed D hS p) κ.1 κ.2.1)
      (κ.1 (attachedNode D hS (p.firstLeaf hS).toNode))
      (nativeCouple_roots_value D hS κ.1 κ.2.1 p) (nativeCouple_noFlower D hS p)
  | .inr b => centerGenDecoration (decodedTree (D.tree b) (nodeSign S.sig b.1))
      (fun a => κ.1 (chainContextNode D hS b a)) (nativeChain_isDecoration D hS κ.1 κ.2.1 b)
      (κ.1 (attachedNode D hS b.toNode)) (nativeChain_roots_value D hS κ.1 b)
      (decodedTree_noFlower (D.tree b) (nodeSign S.sig b.1))

/-- Full decoration recovery is literal nodewise recovery, using the native
node bijection proved from coverage and exact cardinality. -/
theorem glueGenDecoration_restrict {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) :
    glueGenDecoration D hS (collapseGenDecoration D hS κ) (restrictRelativeDecorations D hS κ) = κ := by
  apply Subtype.ext
  funext a
  obtain ⟨⟨s,x⟩,rfl⟩ := (nativeNodeEquiv D hS).surjective a
  have h := glueNativeLabels_at D hS
    (relativeNativeLabels D hS (collapseGenDecoration D hS κ).1 (restrictRelativeDecorations D hS κ)) s x
  apply h.trans
  cases s with
  | inl p => exact sub_add_cancel _ _
  | inr b => exact sub_add_cancel _ _

end WaveTurbulence.RegRed
