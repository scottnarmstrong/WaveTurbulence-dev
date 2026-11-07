/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeChainLeaves
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeNodeEquiv

/-! # Literal leaf transport from all native regular replacements -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

def NativeLeaf {w : ℕ} {S : Garden w} (D : ReconstructionData S) : ReplacementSlot S → Type
  | .inl p => GLeaf (decodedCouple (D.couple p)).tree
  | .inr b => ChainInternalLeaf D b

noncomputable instance {w : ℕ} {S : Garden w} (D : ReconstructionData S) (s : ReplacementSlot S) :
    Fintype (NativeLeaf D s) := by
  cases s <;> dsimp only [NativeLeaf,ChainInternalLeaf] <;> infer_instance

noncomputable def nativeLeafNode {w : ℕ} {S : Garden w} (D : ReconstructionData S) :
    (s : ReplacementSlot S) → NativeLeaf D s → NativeNode D s
  | .inl _,ℓ => ℓ.toNode
  | .inr _,ℓ => ℓ.1.toNode

noncomputable def nativeLeafAt {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) :
    (s : ReplacementSlot S) → NativeLeaf D s → GLeaf (D.forest hS)
  | .inl p,ℓ => (nativeCoupleForest D hS p).leafEmbedding ℓ
  | .inr b,ℓ => chainContextLeaf D hS b ℓ

theorem nativeLeafAt_toNode {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (s : ReplacementSlot S) (ℓ : NativeLeaf D s) :
    (nativeLeafAt D hS s ℓ).toNode = nativeNodeAt D hS s (nativeLeafNode D s ℓ) := by
  cases s with
  | inl p => exact (subforest_node_leaf (nativeCoupleForest D hS p) ℓ).symm
  | inr b => exact chainContextLeaf_toNode D hS b ℓ

theorem nativeLeafNode_injective {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (s : ReplacementSlot S) : Function.Injective (nativeLeafNode D s) := by
  cases s with
  | inl p =>
    intro x y h
    exact Subtype.ext (congrArg (fun a : GNode (decodedCouple (D.couple p)).tree => a.1) h)
  | inr b =>
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg
      (fun a : GNode (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree => a.1) h))

noncomputable def nativeLeafMap {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) :
    (Σ s : ReplacementSlot S, NativeLeaf D s) → GLeaf (D.forest hS) := fun p => nativeLeafAt D hS p.1 p.2

theorem nativeLeafMap_injective {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) : Function.Injective (nativeLeafMap D hS) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ h
  have hnode : nativeNodeMap D hS ⟨i,nativeLeafNode D i x⟩ =
      nativeNodeMap D hS ⟨j,nativeLeafNode D j y⟩ :=
    (nativeLeafAt_toNode D hS i x).symm.trans
      ((congrArg GLeaf.toNode h).trans (nativeLeafAt_toNode D hS j y))
  have he := nativeNodeMap_injective D hS hnode
  have hi := congrArg (fun z : (Σ s : ReplacementSlot S, NativeNode D s) => z.1) he
  change i = j at hi
  subst j
  have hv : nativeLeafNode D i x = nativeLeafNode D i y := by
    exact eq_of_heq (Sigma.mk.inj he).2
  exact congrArg (fun a => Sigma.mk i a) (nativeLeafNode_injective D i hv)

end WaveTurbulence.RegRed
