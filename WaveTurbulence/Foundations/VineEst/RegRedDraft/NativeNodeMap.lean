/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.RegRedDraft.NativeChainNodes
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.NodeCounts

/-! # Literal node coordinates of all native replacements -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

def NativeNode {w : ℕ} {S : Garden w} (D : ReconstructionData S) : ReplacementSlot S → Type
  | .inl p => GNode (decodedCouple (D.couple p)).tree
  | .inr b => GNode (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree

noncomputable instance {w : ℕ} {S : Garden w} (D : ReconstructionData S) (s : ReplacementSlot S) :
    Fintype (NativeNode D s) := by
  cases s <;> dsimp only [NativeNode] <;> infer_instance

noncomputable def nativeNodeAt {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) :
    (s : ReplacementSlot S) → NativeNode D s → GNode (D.forest hS)
  | .inl p,a => (nativeCoupleForest D hS p).nodeEmbedding a
  | .inr b,a => chainContextNode D hS b a

theorem nativeNodeAt_mem_block {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (s : ReplacementSlot S) (a : NativeNode D s) :
    (nativeNodeAt D hS s a).1 ∈ D.nodeBlock hS s := by
  cases s with
  | inl p =>
    change (nativeNodeAt D hS (.inl p) a).1 ∈ coupleNodes (D.couple p)
      (inflatedPosition S D.tree (p.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (p.secondLeaf hS).toNode)
    rw [← couple_nodeAddresses]
    obtain ⟨⟨j,q⟩,hq⟩ := a
    fin_cases j
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨q,hq,rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q,hq,rfl⟩)
  | inr b =>
    change addrExt (inflatedPosition S D.tree b.toNode) a.1.2 ∈
      chainNodes (D.tree b) (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode) ∪
        {addrExt (inflatedPosition S D.tree b.toNode) (D.tree b).lonePath}
    rw [← nodeAddresses_leaf,← chain_nodeAddresses]
    exact Finset.mem_image.mpr ⟨a.1.2,a.2,rfl⟩

theorem nativeNodeAt_injective {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (s : ReplacementSlot S) : Function.Injective (nativeNodeAt D hS s) := by
  cases s with
  | inl p => exact (nativeCoupleForest D hS p).nodeEmbedding.injective
  | inr b =>
    intro x y he
    have hp := congrArg (fun a : GNode (D.forest hS) => a.1.2) he
    exact Subtype.ext (Prod.ext (Subsingleton.elim _ _) (List.append_cancel_left hp))

noncomputable def nativeNodeMap {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) :
    (Σ s : ReplacementSlot S, NativeNode D s) → GNode (D.forest hS) := fun p => nativeNodeAt D hS p.1 p.2

theorem nativeNodeMap_injective {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) : Function.Injective (nativeNodeMap D hS) := by
  obtain ⟨e,he⟩ := exists_replacementNodeEquiv D hS
  rintro ⟨i,x⟩ ⟨j,y⟩ hxy
  let X : Σ s : ReplacementSlot S, ↥(D.nodeBlock hS s) :=
    ⟨i,⟨(nativeNodeAt D hS i x).1,nativeNodeAt_mem_block D hS i x⟩⟩
  let Y : Σ s : ReplacementSlot S, ↥(D.nodeBlock hS s) :=
    ⟨j,⟨(nativeNodeAt D hS j y).1,nativeNodeAt_mem_block D hS j y⟩⟩
  have haddr : X.2.1 = Y.2.1 := congrArg Subtype.val hxy
  have hE : X = Y := e.injective (Subtype.ext ((he X).trans (haddr.trans (he Y).symm)))
  have hi := congrArg (fun z : (Σ s : ReplacementSlot S, ↥(D.nodeBlock hS s)) => z.1) hE
  change i = j at hi
  subst j
  exact congrArg (fun a => Sigma.mk i a) (nativeNodeAt_injective D hS i hxy)

end WaveTurbulence.RegRed
