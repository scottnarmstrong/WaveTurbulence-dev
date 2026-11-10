/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Cnt2
import Mathlib.Tactic

/-!
# The template count, and the new-side count of an LF construction and of a glued construction
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} {S : Garden w} {s : LFSource p kind LG} {ε : Bool}

/-- The count of the template layers on the new objects. -/
@[expose] noncomputable def tcount (X : RegChain) (ζ : ℤˣ) (aT2 : Address w) (To : LayeredGarden w)
    (Q : RegCpl) (Tm : LayeredGarden w) (aT bT : Address w) (p : ℕ) : ℕ :=
  ((((X.plug ζ .leaf).branching).filter (fun q => layerAt To (addrExt aT2 q) = p)).card) +
    coupleSum Q (fun j r => layerAt Tm (addrExt (if j = 0 then aT else bT) r)) p

theorem new_count_of_h (h : LFConstruction s ε) :
    rawTreeLayerCount h.output h.data (s.chosen_plain ε) p (s.branches ε s.placement.lower) +
      rawCoupleLayerCount h.output h.data (s.chosen_plain ε) p (s.pairs ε s.exceptional) =
    tcount h.newTree (nodeSign (s.chosen ε).sig (s.branches ε s.placement.lower).1)
      (inflatedPosition (s.chosen ε) (s.baseData ε).tree (s.branches ε s.placement.lower).toNode)
      h.output h.newCouple (midLayered h)
      (coupleRoot (s.baseData ε) (s.chosen_plain ε) (s.pairs ε s.exceptional) 0)
      (coupleRoot (s.baseData ε) (s.chosen_plain ε) (s.pairs ε s.exceptional) 1) p := by
  unfold tcount
  congr 1
  · rw [rawTreeLayerCount_eq]
    have ht : h.data.tree (s.branches ε s.placement.lower) = h.newTree := Function.update_self _ _ _
    have hpos : inflatedPosition (s.chosen ε) h.data.tree (s.branches ε s.placement.lower).toNode =
        inflatedPosition (s.chosen ε) (s.baseData ε).tree (s.branches ε s.placement.lower).toNode :=
      finalPos_eq (s := s) (ε := ε) h.newTree h.newCouple h.tree_wf h.couple_wf
    rw [ht, hpos]
  · rw [rawCoupleLayerCount_eq]
    have hc : h.data.couple (s.pairs ε s.exceptional) = h.newCouple := Function.update_self _ _ _
    rw [hc]
    refine coupleSum_congr _ _ _ p (fun j r _ => ?_)
    have hT : OutAgreeT (midLayered h) h.output
        (inflatedPosition (s.chosen ε) (s.baseData ε).tree (s.branches ε s.placement.lower).toNode)
        (inflatedPosition (s.chosen ε) (s.baseData ε).tree (s.branches ε s.placement.lower).toNode)
        (addrExt (inflatedPosition (s.chosen ε) (s.baseData ε).tree (s.branches ε s.placement.lower).toNode)
          h.newTree.lonePath) := by
      refine oat_congr rfl ?_ rfl h.treeInsertion.outside
      simp [RegChain.lonePath, addrExt]; rfl
    refine (outC_shift (s := s) (ε := ε) h.newTree h.newCouple h.tree_wf h.couple_wf (midLayered h) h.output hT j r).trans ?_
    fin_cases j <;> rfl

theorem mem_chainNodesSet_of_branching (X : RegChain) (ζ : ℤˣ) (a : Address w) (q : Path)
    (hq : q ∈ (X.plug ζ .leaf).branching) : addrExt a q ∈ chainNodesSet X ζ a := by
  unfold chainNodesSet
  refine Finset.mem_union_left _ ?_
  have hall : pairEndpoints (X.linksAt ζ a) = branchAddresses (X.plug ζ .leaf) a := by
    rw [chain_branchAddresses, branchAddresses_leaf, Finset.union_empty]
  rw [hall]
  exact Finset.mem_image.mpr ⟨q, hq, rfl⟩

theorem new_count_of_glue (g : GlueSpec s ε) :
    rawTreeLayerCount g.glued2 g.FD (s.chosen_plain ε) p (s.branches ε s.placement.lower) +
      rawCoupleLayerCount g.glued2 g.FD (s.chosen_plain ε) p (s.pairs ε s.exceptional) =
    tcount g.X (nodeSign (s.chosen ε).sig (s.branches ε s.placement.lower).1) g.aT2 g.To g.Q g.Tm g.aT g.bT p := by
  unfold tcount
  congr 1
  · rw [rawTreeLayerCount_eq]
    rw [g.FD_tree_lower]
    congr 1
    refine Finset.filter_congr (fun q hq => ?_)
    have hx : addrExt (inflatedPosition (s.chosen ε) g.FD.tree (s.branches ε s.placement.lower).toNode) q ∈
        chainNodesSet (g.FD.tree (s.branches ε s.placement.lower))
          (nodeSign (s.chosen ε).sig (s.branches ε s.placement.lower).1)
          (inflatedPosition (s.chosen ε) g.FD.tree (s.branches ε s.placement.lower).toNode) := by
      rw [g.FD_tree_lower]
      exact mem_chainNodesSet_of_branching _ _ _ _ hq
    have := g.glueT.glued_region ⟨chainNodesSet_under hx, chainNodesSet_not_under_lone hx⟩
    rw [treePort_ext] at this
    rw [show g.glued2 = g.glueT.glued from rfl, this]
  · rw [rawCoupleLayerCount_eq]
    have hc : g.FD.couple (s.pairs ε s.exceptional) = g.Q := Function.update_self _ _ _
    rw [hc]
    have hT : OutAgreeT g.glued1 g.glued2
        (inflatedPosition (s.chosen ε) (s.baseData ε).tree (s.branches ε s.placement.lower).toNode)
        (inflatedPosition (s.chosen ε) (s.baseData ε).tree (s.branches ε s.placement.lower).toNode)
        (addrExt (inflatedPosition (s.chosen ε) (s.baseData ε).tree (s.branches ε s.placement.lower).toNode)
          g.X.lonePath) := by
      refine oat_congr g.pos_FD g.pos_FD ?_ g.glueT.outAgreeT
      rw [g.FD_tree_lower, g.pos_FD]
      rfl
    refine coupleSum_congr _ _ _ p (fun j r _ => ?_)
    refine (outC_shift (s := s) (ε := ε) g.X g.Q g.hX g.hQ g.glued1 g.glued2 hT j r).trans ?_
    have hcl := g.glueC
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

end WaveTurbulence.Stage1
