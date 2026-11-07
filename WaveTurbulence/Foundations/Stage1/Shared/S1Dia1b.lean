/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Dia1
import Mathlib.Tactic

/-!
# Template regions of a glued output
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool}

theorem glue_region_tree (g : GlueSpec s ε) (q : Path)
    (hq : q ∈ (g.X.plug (nodeSign (s.chosen ε).sig (s.branches ε s.placement.lower).1) .leaf).branching) :
    layerAt g.glued2 (addrExt (inflatedPosition (s.chosen ε) g.FD.tree (s.branches ε s.placement.lower).toNode) q) =
      layerAt g.To (addrExt g.aT2 q) := by
  have hx : addrExt (inflatedPosition (s.chosen ε) g.FD.tree (s.branches ε s.placement.lower).toNode) q ∈
      chainNodesSet (g.FD.tree (s.branches ε s.placement.lower))
        (nodeSign (s.chosen ε).sig (s.branches ε s.placement.lower).1)
        (inflatedPosition (s.chosen ε) g.FD.tree (s.branches ε s.placement.lower).toNode) := by
    rw [g.FD_tree_lower]
    exact mem_chainNodesSet_of_branching _ _ _ _ hq
  have := g.glueT.glued_region ⟨chainNodesSet_under hx, chainNodesSet_not_under_lone hx⟩
  rw [treePort_ext] at this
  rw [show g.glued2 = g.glueT.glued from rfl, this]

theorem glue_region_couple (g : GlueSpec s ε) (j : Fin 2) (r : Path) :
    layerAt g.glued2 (addrExt (coupleRoot g.FD (s.chosen_plain ε) (s.pairs ε s.exceptional) j) r) =
      layerAt g.Tm (addrExt (if j = 0 then g.aT else g.bT) r) := by
  have hT : OutAgreeT g.glued1 g.glued2
      (inflatedPosition (s.chosen ε) (s.baseData ε).tree (s.branches ε s.placement.lower).toNode)
      (inflatedPosition (s.chosen ε) (s.baseData ε).tree (s.branches ε s.placement.lower).toNode)
      (addrExt (inflatedPosition (s.chosen ε) (s.baseData ε).tree (s.branches ε s.placement.lower).toNode)
        g.X.lonePath) := by
    refine oat_congr g.pos_FD g.pos_FD ?_ g.glueT.outAgreeT
    rw [g.FD_tree_lower, g.pos_FD]
    rfl
  refine (outC_shift (s := s) (ε := ε) g.X g.Q g.hX g.hQ g.glued1 g.glued2 hT j r).trans ?_
  fin_cases j
  · have hz : InRegion
        (inflatedPosition (s.chosen ε) (s.midData ε g.Q g.hQ).tree
          ((s.pairs ε s.exceptional).firstLeaf (s.chosen_plain ε)).toNode)
        (inflatedPosition (s.chosen ε) (s.midData ε g.Q g.hQ).tree
          ((s.pairs ε s.exceptional).secondLeaf (s.chosen_plain ε)).toNode)
        (addrExt (inflatedPosition (s.chosen ε) (s.midData ε g.Q g.hQ).tree
          ((s.pairs ε s.exceptional).firstLeaf (s.chosen_plain ε)).toNode) r) := Or.inl (under_ext _ _)
    have := g.glueC.glued_region hz
    rw [couplePort_a _ _ _ _ g.glueC.indep] at this
    exact this
  · have hz : InRegion
        (inflatedPosition (s.chosen ε) (s.midData ε g.Q g.hQ).tree
          ((s.pairs ε s.exceptional).firstLeaf (s.chosen_plain ε)).toNode)
        (inflatedPosition (s.chosen ε) (s.midData ε g.Q g.hQ).tree
          ((s.pairs ε s.exceptional).secondLeaf (s.chosen_plain ε)).toNode)
        (addrExt (inflatedPosition (s.chosen ε) (s.midData ε g.Q g.hQ).tree
          ((s.pairs ε s.exceptional).secondLeaf (s.chosen_plain ε)).toNode) r) := Or.inr (under_ext _ _)
    have := g.glueC.glued_region hz
    rw [couplePort_b _ _ _ _ g.glueC.indep] at this
    exact this

theorem h_couple_region (h : LFConstruction s ε) (j : Fin 2) (r : Path) :
    layerAt h.output (addrExt (coupleRoot h.data (s.chosen_plain ε) (s.pairs ε s.exceptional) j) r) =
      layerAt (midLayered h) (addrExt (if j = 0 then
        coupleRoot (s.baseData ε) (s.chosen_plain ε) (s.pairs ε s.exceptional) 0
        else coupleRoot (s.baseData ε) (s.chosen_plain ε) (s.pairs ε s.exceptional) 1) r) := by
  have hT : OutAgreeT (midLayered h) h.output
      (inflatedPosition (s.chosen ε) (s.baseData ε).tree (s.branches ε s.placement.lower).toNode)
      (inflatedPosition (s.chosen ε) (s.baseData ε).tree (s.branches ε s.placement.lower).toNode)
      (addrExt (inflatedPosition (s.chosen ε) (s.baseData ε).tree (s.branches ε s.placement.lower).toNode)
        h.newTree.lonePath) := by
    refine oat_congr rfl ?_ rfl h.treeInsertion.outside
    simp [RegChain.lonePath, addrExt]; rfl
  refine (outC_shift (s := s) (ε := ε) h.newTree h.newCouple h.tree_wf h.couple_wf (midLayered h) h.output hT j r).trans ?_
  fin_cases j <;> rfl

end WaveTurbulence.Stage1
