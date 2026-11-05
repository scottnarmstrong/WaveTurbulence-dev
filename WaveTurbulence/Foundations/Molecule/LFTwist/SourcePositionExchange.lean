/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.CrownFrames
public import WaveTurbulence.Foundations.Molecule.LFTwist.CommonFrames
public import WaveTurbulence.Foundations.Molecule.LFTwist.InflationGeometry

/-! # Literal source-node positions commute with the expanded exchange -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist Links
variable {w : ℕ} (S : Garden w) (P : CorePlacement S) (hS : S.IsPlain) (D : ReconstructionData S)

/-- Every source node outside the removed crown survives in the common forest. -/
theorem common_node_of_outside (n : GNode S.tree) (hn : ¬ Below P.lower.1 n.1) :
    n.1.2 ∈ (commonForest S P.lower n.1.1).nodes := by
  apply (Comb.TreePath.mem_nodes_iff _ _).mpr
  rcases (Comb.TreePath.mem_nodes_iff _ _).mp n.2 with hl | hb
  · exact Or.inl ((collapseNodeForest_leaf_iff S.tree P.lower.toNode n.1).mpr (Or.inl ⟨hl,hn⟩))
  · exact Or.inr ((collapseNodeForest_branch_iff S.tree P.lower.toNode n.1).mpr ⟨hb,hn⟩)

/-- The two physical hole addresses agree for the old and transported assignments. -/
theorem hole_rawSourcePosition_twist (a : Address w)
    (ha : a = P.lower.1 ∨ a = (S.pair P.retained).1) :
    rawSourcePosition (twistReconstruction S P hS D) a = rawSourcePosition D a := by
  rcases ha with rfl | rfl
  · exact common_rawSourcePosition_twist S P hS D (collapsedRoot S P.lower).toNode
  · exact common_rawSourcePosition_twist S P hS D (pairedHole S P).toNode

/-- Actual reconstruction positions intertwine the source and physical exchanges.
This position statement does not require triviality of the exceptional couple. -/
theorem rawSourcePosition_exchange (hnil : D.tree P.lower = .nil) (n : GNode S.tree) :
    rawSourcePosition (twistReconstruction S P hS D)
      (exchangeAddress P.lower.1 (S.pair P.retained).1 P.keep n.1) =
    exchangeAddress (rawSourcePosition D P.lower.1) (rawSourcePosition D (S.pair P.retained).1)
      P.keep (rawSourcePosition D n.1) := by
  by_cases hn : Below P.lower.1 n.1
  · obtain ⟨q,hq⟩ := hn.2
    have hv : n.1 = addrExt P.lower.1 q := Prod.ext hn.1 hq.symm
    have hm : q ∈ (lowerCrown S P.lower).nodes := by
      have hh := (Comb.subtree_nodes_iff (Mole.spliceNodeSubtree_spec S P.lower.toNode) q)
      apply hh.mpr
      have hh : n.1.2 ∈ (S.tree n.1.1).nodes := n.2
      rw [hv] at hh
      exact hh
    rw [hv]
    have hex : exchangeAddress P.lower.1 (S.pair P.retained).1 P.keep (addrExt P.lower.1 q) =
        addrExt (S.pair P.retained).1 (switchPath P.keep q) := by
      simp [exchangeAddress, addrExt]
    rw [hex, rawSourcePosition_append, hole_rawSourcePosition_twist S P hS D _ (Or.inr rfl),
      crown_frame_twist S P hS D hnil q hm, rawSourcePosition_append]
    simp [exchangeAddress, addrExt]
  · by_cases hp : n.1 = (S.pair P.retained).1
    · rw [hp]
      have hnot : ¬ ((S.pair P.retained).1.1 = P.lower.1.1 ∧ P.lower.1.2 <+: (S.pair P.retained).1.2) :=
        fun he => P.paired_outside ⟨he.1.symm,he.2⟩
      have hnot' : ¬ ((rawSourcePosition D (S.pair P.retained).1).1 =
          (rawSourcePosition D P.lower.1).1 ∧
          (rawSourcePosition D P.lower.1).2 <+: (rawSourcePosition D (S.pair P.retained).1).2) := by
        intro he
        have hh : Below (inflatedPosition S D.tree P.lower.toNode)
            (inflatedPosition S D.tree (S.pair P.retained).toNode) := by
          rw [inflatedPosition_eq_rawSourcePosition D P.lower.toNode,
            inflatedPosition_eq_rawSourcePosition D (S.pair P.retained).toNode]
          exact he
        exact hnot ((inflatedPosition_below_iff S D.tree P.lower.toNode (S.pair P.retained).toNode).mp hh)
      simp only [exchangeAddress, hnot, hnot', ite_false, ite_true]
      exact hole_rawSourcePosition_twist S P hS D _ (Or.inl rfl)
    · have hnot' : ¬ ((rawSourcePosition D n.1).1 = (rawSourcePosition D P.lower.1).1 ∧
          (rawSourcePosition D P.lower.1).2 <+: (rawSourcePosition D n.1).2) := by
        intro he
        have hh : Below (inflatedPosition S D.tree P.lower.toNode) (inflatedPosition S D.tree n) := by
          rw [inflatedPosition_eq_rawSourcePosition D P.lower.toNode, inflatedPosition_eq_rawSourcePosition D n]
          exact he
        exact hn ((inflatedPosition_below_iff S D.tree P.lower.toNode n).mp hh)
      have hp' : rawSourcePosition D n.1 ≠ rawSourcePosition D (S.pair P.retained).1 := by
        intro he
        have hh : inflatedPosition S D.tree n = inflatedPosition S D.tree (S.pair P.retained).toNode := by
          rw [inflatedPosition_eq_rawSourcePosition D n,
            inflatedPosition_eq_rawSourcePosition D (S.pair P.retained).toNode]
          exact he
        exact hp (congrArg Subtype.val (inflatedPosition_injective S D.tree hh))
      simp only [exchangeAddress, show ¬ (n.1.1 = P.lower.1.1 ∧ P.lower.1.2 <+: n.1.2) from hn,
        hp, hnot', hp', ite_false]
      exact common_rawSourcePosition_twist S P hS D ⟨n.1,common_node_of_outside S P n hn⟩

end WaveTurbulence.LFTwist
