/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1TrF4
import Mathlib.Tactic

/-!
# Layer facts of an LF construction used when it is transported to another source
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} {S : Garden w}

theorem finalPos_eq {s : LFSource p kind LG} {ε : Bool} (X : RegChain) (Q : RegCpl) (hX : X.wf = true) (hQ : Q.wf = true) :
    inflatedPosition (s.chosen ε) (s.finalData ε X Q hX hQ).tree (s.branches ε s.placement.lower).toNode =
      inflatedPosition (s.chosen ε) (s.baseData ε).tree (s.branches ε s.placement.lower).toNode := by
  have := ((s.finalData ε X Q hX hQ).eraseTree_position_at (s.branches ε s.placement.lower)).symm
  rw [eraseTree_final] at this
  exact this

theorem lower_not_in_region (s : LFSource p kind LG) (ε : Bool) :
    ¬ InRegion (inflatedPosition (s.chosen ε) (s.baseData ε).tree
        ((s.pairs ε s.exceptional).firstLeaf (s.chosen_plain ε)).toNode)
      (inflatedPosition (s.chosen ε) (s.baseData ε).tree
        ((s.pairs ε s.exceptional).secondLeaf (s.chosen_plain ε)).toNode)
      (inflatedPosition (s.chosen ε) (s.baseData ε).tree (s.branches ε s.placement.lower).toNode) := by
  rintro (h | h)
  · exact leaf_not_above_branch (s.chosen ε).tree _ _
      ((inflatedPosition_below_iff _ _ _ _).mp ((under_iff_below_addr _ _).mp h))
  · exact leaf_not_above_branch (s.chosen ε).tree _ _
      ((inflatedPosition_below_iff _ _ _ _).mp ((under_iff_below_addr _ _).mp h))

theorem coupleRoot_zero (D : ReconstructionData S) (hS : S.IsPlain) (q : SourcePair S) :
    coupleRoot D hS q 0 = inflatedPosition S D.tree (q.firstLeaf hS).toNode := by simp [coupleRoot]

theorem coupleRoot_one (D : ReconstructionData S) (hS : S.IsPlain) (q : SourcePair S) :
    coupleRoot D hS q 1 = inflatedPosition S D.tree (q.secondLeaf hS).toNode := by simp [coupleRoot]

variable {s : LFSource p kind LG} {ε : Bool} (h : LFConstruction s ε)

theorem h_par_a : parAt (s.base ε) p (coupleRoot (s.baseData ε) (s.chosen_plain ε) (s.pairs ε s.exceptional) 0) =
    parAt (midLayered h) p (coupleRoot (s.baseData ε) (s.chosen_plain ε) (s.pairs ε s.exceptional) 0) :=
  h.coupleInsertion.outside.parAt_eq_a h.coupleInsertion.newEmbedding.indep
    h.coupleInsertion.oldEmbedding.nodeA h.coupleInsertion.newEmbedding.nodeA

theorem h_par_b : parAt (s.base ε) p (coupleRoot (s.baseData ε) (s.chosen_plain ε) (s.pairs ε s.exceptional) 1) =
    parAt (midLayered h) p (coupleRoot (s.baseData ε) (s.chosen_plain ε) (s.pairs ε s.exceptional) 1) :=
  h.coupleInsertion.outside.parAt_eq_b h.coupleInsertion.newEmbedding.indep
    h.coupleInsertion.oldEmbedding.nodeB h.coupleInsertion.newEmbedding.nodeB

theorem h_par_lower : parAt h.output p (inflatedPosition (s.chosen ε) (s.baseData ε).tree
      (s.branches ε s.placement.lower).toNode) =
    parAt (s.base ε) p (inflatedPosition (s.chosen ε) (s.baseData ε).tree (s.branches ε s.placement.lower).toNode) := by
  have e1 : parAt (midLayered h) p (inflatedPosition (s.chosen ε) (s.baseData ε).tree
      (s.branches ε s.placement.lower).toNode) = parAt h.output p (inflatedPosition (s.chosen ε)
      (s.baseData ε).tree (s.branches ε s.placement.lower).toNode) :=
    OutAgreeT.parAt_root_eq (X := RegChain.nil) (X' := h.newTree) h.treeInsertion.outside
      h.treeInsertion.oldEmbedding.node h.treeInsertion.newEmbedding.node
  have hn1 : (inflatedPosition (s.chosen ε) (s.baseData ε).tree (s.branches ε s.placement.lower).toNode).2 ∈
      ((s.base ε).garden.tree (inflatedPosition (s.chosen ε) (s.baseData ε).tree
        (s.branches ε s.placement.lower).toNode).1).nodes :=
    ((s.baseData ε).decodedNode (s.chosen_plain ε) (s.base_decodes ε) (s.branches ε s.placement.lower).toNode).2
  have e2 := h.coupleInsertion.outside.parAt_eq_out (p := p) (lower_not_in_region s ε) hn1
    h.treeInsertion.oldEmbedding.node
  exact e1.symm.trans e2.symm

theorem h_lone : layerAt h.output (addrExt (inflatedPosition (s.chosen ε) (s.baseData ε).tree
      (s.branches ε s.placement.lower).toNode) h.newTree.lonePath) =
    layerAt LG (s.data.corePosition s.placement.lower) := by
  have := h.coreLayers s.placement.lower
  have hcore : (s.finalData ε h.newTree h.newCouple h.tree_wf h.couple_wf).corePosition
      (s.branches ε s.placement.lower) = addrExt (inflatedPosition (s.chosen ε) (s.baseData ε).tree
        (s.branches ε s.placement.lower).toNode) h.newTree.lonePath := by
    unfold ReconstructionData.corePosition
    rw [finalPos_eq]
    have ht : (s.finalData ε h.newTree h.newCouple h.tree_wf h.couple_wf).tree (s.branches ε s.placement.lower) =
      h.newTree := Function.update_self _ _ _
    rw [ht]
  rw [this, hcore]
  rfl

end WaveTurbulence.Stage1
