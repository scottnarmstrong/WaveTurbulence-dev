/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistNonroot

/-! # Actual parent transport away from the exchanged PC/LP incidences -/

public section
namespace WaveTurbulence.Twist
open TTree

/-- An actual child address determines its actual parent. -/
theorem parent_eq_of_child {w : ℕ} {F : Fin w → TTree} {n : GNode F} {p : GBranch F}
    {i : Fin 3} (hn : n.1.2 ≠ []) (hc : n = p.child i) : GNode.parent n hn = p := by
  apply Subtype.ext
  change (n.1.1,n.1.2.dropLast) = p.1
  have hv : n.1 = (p.1.1,p.1.2 ++ [i]) := congrArg Subtype.val hc
  rw [hv]
  simp

variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- Ordinary nonroot branches keep their actual parent under branch transport. -/
theorem branchParent_transport (c : GBranch G.tree) (hn : c.1.2 ≠ []) (hc : c ≠ P.lower) :
    GNode.parent (coreBranchEquiv G P c).toNode ((coreBranchEquiv_nonroot G P c).mpr hn) =
      coreBranchEquiv G P (GNode.parent c.toNode hn) := by
  apply parent_eq_of_child
  exact branch_child_transport G P (Mole.parent_child_eq_node c.toNode hn).symm hc

/-- Ordinary nonroot LP leaves keep their actual parent under leaf transport. -/
theorem leafParent_transport (l : GLeaf G.tree) (hn : l.1.2 ≠ []) (hl : l ≠ G.pair P.retained) :
    GNode.parent (coreLeafEquiv G P l).toNode ((coreLeafEquiv_nonroot G P l).mpr hn) =
      coreBranchEquiv G P (GNode.parent l.toNode hn) := by
  apply parent_eq_of_child
  exact leaf_child_transport G P (Mole.parent_child_eq_node l.toNode hn).symm hl

/-- A branching node outside the removed subtree keeps its exact address. -/
theorem coreBranchEquiv_fixed_val (b : GBranch G.tree) (hout : ¬ P.lower.toNode.IsDesc b.toNode) :
    (coreBranchEquiv G P b).1 = b.1 := by
  rw [coreBranchEquiv_address]
  have hn : ¬ (b.1.1 = P.lower.1.1 ∧ P.lower.1.2 <+: b.1.2) :=
    fun h => hout ⟨h.1.symm,h.2⟩
  simp [exchangeAddress,hn,branch_ne_paired_address G P b]

/-- The old lower parent is outside the lower subtree. -/
theorem lower_parent_outside : ¬ P.lower.toNode.IsDesc (GNode.parent P.lower.toNode P.nonroot).toNode := by
  intro hd
  have hh := Molecpl.parent_length G P.lower.toNode P.nonroot
  have hl := hd.2.length_le
  dsimp [GBranch.toNode,GNode.parent] at hh hl
  omega

/-- The old parent of u0 is outside the lower subtree. -/
theorem paired_parent_outside : ¬ P.lower.toNode.IsDesc
    (GNode.parent (G.pair P.retained).toNode P.paired_nonroot).toNode := by
  intro hd
  apply P.paired_outside
  have hdesc : (GNode.parent (G.pair P.retained).toNode P.paired_nonroot).toNode.IsDesc
      (G.pair P.retained).toNode := by
    exact ⟨rfl,List.dropLast_prefix _⟩
  exact ⟨hd.1.trans hdesc.1,hd.2.trans hdesc.2⟩

end WaveTurbulence.Twist
