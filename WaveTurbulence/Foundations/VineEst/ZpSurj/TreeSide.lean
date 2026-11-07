/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.CoupleSide

/-! # ZP-SURJ: the garden-level data of a tree reinsertion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ZpSurj
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ}

/-- The tail subtree at the nil chain, the two embeddings and the garden-level shift agreement. -/
theorem tree_side {S : Garden w} (hS : S.IsPlain) (D1 : ReconstructionData S) (b : GBranch S.tree)
    (hnil : D1.tree b = .nil) (X : RegChain) (hX : X.wf = true) :
    ∃ t : TTree,
      ChainEmb (D1.garden hS) .nil (nodeSign S.sig b.1) (inflatedPosition S D1.tree b.toNode) t ∧
      ChainEmb ((D1.withTree b X hX).garden hS) X (nodeSign S.sig b.1) (inflatedPosition S D1.tree b.toNode) t ∧
      GOutT (D1.garden hS) ((D1.withTree b X hX).garden hS) (inflatedPosition S D1.tree b.toNode)
        (addrExt (inflatedPosition S D1.tree b.toNode) X.lonePath) := by
  set D := D1.withTree b X hX with hD
  have hE : D.eraseTree b = D1 := by
    apply ReconstructionData.ext_tree_couple
    · change Function.update (Function.update D1.tree b X) b .nil = D1.tree
      rw [Function.update_idem, ← hnil]
      exact Function.update_eq_self _ _
    · rfl
  have hDt : D.tree b = X := Function.update_self _ _ _
  let LGz := zeroLayered (D.garden hS)
  let hd := D.garden_decodes hS
  have h : Comb.IsSubPairedTree LGz.garden (D.decodedNode hS hd b.toNode) (D.decodedCoreNode hS hd b) :=
    D.decoded_chain_isSubPairedTree hS hd b
  have hdec := eraseTree_collapse_decodes D hS hd b
  rw [hE] at hdec
  have hG : D1.garden hS = collapsePairedTreeGarden h :=
    rawOfGarden_injective_plain (D1.garden_plain hS) hdec.1 ((D1.garden_raw hS).trans hdec.2)
  have hpos : inflatedPosition S D.tree b.toNode = inflatedPosition S D1.tree b.toNode := by
    rw [← hE]; exact (D.eraseTree_position_at b).symm
  have hs : Comb.nodeSubtree (D.decodedCoreNode hS hd b) = node3 (fun i => D.inflateNode hS (b.child i)) :=
    Option.some.inj ((Comb.nodeSubtree_spec (D.decodedCoreNode hS hd b)).symm.trans (D.decoded_subtree_core hS hd b))
  refine ⟨Comb.nodeSubtree (D.decodedCoreNode hS hd b), ?_, ?_, ?_⟩
  · have := collapsePairedTree_embeds_nil LGz h (nodeSign S.sig b.1)
    rw [hG, ← hpos]; exact this
  · have := reconstruction_chainEmb D hS hd b
    rw [hDt, ← hs, hpos] at this
    exact this
  · have hA := collapsePairedTree_outAgree LGz h
    have hb : (D.decodedCoreNode hS hd b).1 = addrExt (D.decodedNode hS hd b.toNode).1 X.lonePath := by
      rw [← hDt]; rfl
    have hC : ChainEmb (D.garden hS) X (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode)
        (Comb.nodeSubtree (D.decodedCoreNode hS hd b)) := by
      have := reconstruction_chainEmb D hS hd b
      rw [hDt, ← hs] at this
      exact this
    have e0 : ∀ x : Fin w × Path, addrExt x RegChain.nil.lonePath = x := fun x => addrExt_nil x
    have hA' : OutAgreeT LGz (collapsePairedTreeLayered LGz h) (D.decodedNode hS hd b.toNode).1
        (addrExt (D.decodedNode hS hd b.toNode).1 X.lonePath)
        (addrExt (D.decodedNode hS hd b.toNode).1 RegChain.nil.lonePath) := by
      rw [e0, ← hb]; exact hA
    have hS' := hA'.symm hC
    rw [e0] at hS'
    have hz0 : ∀ z : Fin w × Path, ¬ InTree (D.decodedNode hS hd b.toNode).1
        (D.decodedNode hS hd b.toNode).1 z := by
      intro z hz
      exact hz.2 hz.1
    have e1 : (D.decodedNode hS hd b.toNode).1 = inflatedPosition S D1.tree b.toNode := hpos
    rw [hG]
    rw [← e1]
    exact ⟨fun z => hS'.node z (hz0 z), fun z => hS'.leaf z (hz0 z), fun ℓ ℓ' he => hS'.pair ℓ ℓ' (hz0 _) he⟩

end WaveTurbulence.ZpSurj
