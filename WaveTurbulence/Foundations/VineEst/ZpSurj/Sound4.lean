/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Sound3

/-! # ZP-SURJ soundness: the exceptional datum of an arbitrary construction -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.ZpSurj
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.Stage1

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool}
  (con : LFConstruction s ε)

theorem conLX_layer {r : Path} (hr : r ∈ (con.newTree.plug (srcSign s ε) .leaf).nodes) :
    layerAt con.output (addrExt (tA s ε) r) = layerAt (conLX con) ((0 : Fin 1), r) := by
  have hFD : con.data.tree (s.branches ε s.placement.lower) = con.newTree := Function.update_self _ _ _
  have hz : r ∈ ((decodedTree (con.data.tree (s.branches ε s.placement.lower))
      (nodeSign (s.chosen ε).sig (s.branches ε s.placement.lower).1)).tree 0).nodes := by
    rw [hFD]; exact hr
  have h := VineEstS4.layerAt_nativeTree con.data (s.chosen_plain ε) con.outLayer con.out_isLayering
    (s.branches ε s.placement.lower) ((0 : Fin 1), r) hz
  have hp := pos_final (s := s) (ε := ε) con.newCouple con.couple_wf con.newTree con.tree_wf
  refine Eq.trans ?_ h.symm
  change layerAt con.output (addrExt (tA s ε) r) =
    layerAt con.output (addrExt (inflatedPosition (s.chosen ε) con.data.tree (s.branches ε s.placement.lower).toNode) r)
  exact congrArg (fun z => layerAt con.output (addrExt z r)) hp.symm

theorem conMid_layer_tA : layerAt (conMid con) (tA s ε) = layerAt (s.base ε) (tA s ε) := by
  have hout := con.coupleInsertion.outside
  rw [coupleRoot_zero, coupleRoot_one] at hout
  exact (hout.layer _ (notRegion_tA con.newCouple con.couple_wf)).symm

theorem conMid_parAt_tA : parAt (conMid con) p (tA s ε) = parAt (s.base ε) p (tA s ε) := by
  have hout := con.coupleInsertion.outside
  rw [coupleRoot_zero, coupleRoot_one] at hout
  have hz : (tA s ε).2 ∈ ((s.base ε).garden.tree (tA s ε).1).nodes :=
    ((s.baseData ε).decodedNode (s.chosen_plain ε) (s.base_decodes ε) (s.branches ε s.placement.lower).toNode).2
  have hz' : (tA s ε).2 ∈ ((conMid con).garden.tree (tA s ε).1).nodes :=
    ((s.midData ε con.newCouple con.couple_wf).decodedNode (s.chosen_plain ε)
      ((s.midData ε con.newCouple con.couple_wf).garden_decodes _) (s.branches ε s.placement.lower).toNode).2
  exact (hout.symm.parAt_eq_out (notRegion_tA con.newCouple con.couple_wf) hz' hz)

theorem conLX_lone : layerAt (conLX con) ((0 : Fin 1), con.newTree.lonePath) = layerAt (s.base ε) (tA s ε) := by
  have hlone := lone_mem_nodes con.newTree (srcSign s ε)
  rw [← conLX_layer con hlone]
  have hT := con.treeInsertion.outside
  generalize ha0 : inflatedPosition (s.chosen ε) (s.midData ε con.newCouple con.couple_wf).tree
    (s.branches ε s.placement.lower).toNode = a0 at hT
  have ha0' : a0 = tA s ε := ha0.symm
  have h1 := hT.layer (addrExt a0 RegChain.nil.lonePath) (fun h => h.2 (under_refl _))
  have e : shiftAddr (addrExt a0 RegChain.nil.lonePath) (addrExt a0 con.newTree.lonePath)
      (addrExt a0 RegChain.nil.lonePath) = addrExt a0 con.newTree.lonePath := by
    simp [shiftAddr, under_refl, addrExt]
  rw [e] at h1
  subst ha0'
  rw [← conMid_layer_tA con]
  simp only [RegChain.lonePath, addrExt_nil] at h1
  exact h1.symm

end WaveTurbulence.ZpSurj
