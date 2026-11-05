/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.RegRedDraft.NativeChainDecorations
public import WaveTurbulence.Foundations.Molecule.RegRedDraft.NativeCoupleLayering
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Gardens

/-! # Attachment momenta follow from actual conservation and actual leaf pairing -/

public section
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

theorem pairedTree_lone_eq_root {G : Garden 1} (hG : IsPairedTree G)
    {V : Type*} [AddCommGroup V] (κ : GNode G.tree → V) (hκ : IsDecoration G κ)
    (ℓ : GLeaf G.tree) (hℓ : G.IsLone ℓ) : κ ℓ.toNode = κ (GNode.root G.tree 0) := by
  have h := hG.lone_value hκ hℓ
  have hr : G.sign (GNode.root G.tree 0) = G.sig 0 := by
    simp only [Garden.sign,nodeSign,GNode.root,pathSign,List.count_nil,pow_zero,mul_one]
  rw [hG.sign_lone hℓ,hr] at h
  exact (G.sig 0).isUnit.smul_left_cancel.mp h

theorem chainContextNode_root {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (b : GBranch S.tree) :
    chainContextNode D hS b (GNode.root _ 0) = attachedNode D hS b.toNode := by
  apply Subtype.ext
  exact Prod.ext rfl (List.append_nil _)

theorem chainContextNode_lone {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (b : GBranch S.tree) :
    chainContextNode D hS b (chainLoneLeaf (D.tree b) (nodeSign S.sig b.1)).toNode =
      (D.coreBranch hS b).toNode := Subtype.ext rfl

/-- TARGET regred: the upper and lower attachments of every actual regular-tree
replacement carry the same momentum; no endpoint equation is assumed. -/
theorem chain_attachment_momentum {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) {V : Type*} [AddCommGroup V] (κ : GNode (D.forest hS) → V)
    (hκ : IsDecoration (D.garden hS) κ) (b : GBranch S.tree) :
    κ (attachedNode D hS b.toNode) = κ (D.coreBranch hS b).toNode := by
  have h := pairedTree_lone_eq_root (decodedTree_isPairedTree (D.tree b) (nodeSign S.sig b.1))
    (fun a => κ (chainContextNode D hS b a)) (nativeChain_isDecoration D hS κ hκ b)
    (chainLoneLeaf (D.tree b) (nodeSign S.sig b.1))
    ((decodesTree_lone_iff (decodedTree_decodes _ _) _).mpr rfl)
  exact (congrArg κ (chainContextNode_root D hS b)).symm.trans
    (h.symm.trans (congrArg κ (chainContextNode_lone D hS b)))

theorem couple_attachment_momentum {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) {V : Type*} [AddCommGroup V] (κ : GNode (D.forest hS) → V)
    (hκ : IsDecoration (D.garden hS) κ) (p : SourcePair S) :
    κ (attachedNode D hS (p.firstLeaf hS).toNode) =
      κ (attachedNode D hS (p.secondLeaf hS).toNode) := by
  let E := nativeCoupleForest D hS p
  let H := Comb.RootedSubforest.inducedGarden (G := D.garden hS) E (nativeCoupleForest_closed D hS p)
  let η : GNode H.tree → V := fun a => κ (E.nodeEmbedding a)
  have hd : IsDecoration H η := subforest_isDecoration (D.garden hS) E _ κ hκ
  have he : H = decodedCouple (D.couple p) := nativeCoupleGarden_eq D hS p
  have hp := Comb.sum_signed_roots_eq_zero (G := H) (by rw [he]; exact (decodedCouple_decodes _).1.1) hd
  have hs : H.sig = ![1,-1] := by rw [he]; rfl
  rw [Fin.sum_univ_two,hs] at hp
  change (1 : ℤ) • η (GNode.root H.tree 0) + (-1 : ℤ) • η (GNode.root H.tree 1) = 0 at hp
  simp only [one_smul,neg_smul] at hp
  have hr := eq_of_sub_eq_zero (show η (GNode.root H.tree 0) - η (GNode.root H.tree 1) = 0 from (by simpa only [sub_eq_add_neg] using hp))
  have h0 := congrArg κ (subforest_node_root E 0)
  have h1 := congrArg κ (subforest_node_root E 1)
  exact h0.symm.trans (hr.trans h1)

end WaveTurbulence.RegRed
