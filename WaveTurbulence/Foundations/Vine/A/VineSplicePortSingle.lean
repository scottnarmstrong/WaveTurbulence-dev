/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineSplicePortAddress
/-! Port preservation for the literal branch and leaf names of one CL splice. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Mole TTree
variable {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b)
    (D : CLSpliceSlots G S a b)

/-- A retained branching child keeps its slot when its old parent survives. -/
theorem cl_branch_port_of_parent_kept (c : GBranch (clSplicedGardenOfSlots hB hCL D).tree)
    (hn : c.1.2 ≠ []) (ho : (clSplicedBranchNameEquiv hB hCL D c).1.1.2 ≠ [])
    (hp : GNode.parent (clSplicedBranchNameEquiv hB hCL D c).1.toNode ho ∉ S ∨
      GNode.parent (clSplicedBranchNameEquiv hB hCL D c).1.toNode ho = a) :
    c.1.2.getLast hn = (clSplicedBranchNameEquiv hB hCL D c).1.1.2.getLast ho := by
  classical
  by_cases hc : c = spliceCrownBranch (clSpliceBoundary hB hCL D)
  · subst c
    simp only [clSplicedBranchName_crown] at ho ⊢
    rfl
  · obtain ⟨p, rfl⟩ := spliceBranchPieceNew_surjective_except_crown (clSpliceBoundary hB hCL D) c hc
    simp only [clSplicedBranchName_piece] at ho hp ⊢
    cases p with
    | inl c => rfl
    | inr p =>
      exact cl_inside_port hB hCL D p.1 p.2.1 (TTree.branching_subset_nodes _ p.2.2) ho hn hp

/-- A retained leaf keeps its slot when its old parent survives, including marked leaves. -/
theorem cl_leaf_port_of_parent_kept (l : GLeaf (clSplicedGardenOfSlots hB hCL D).tree)
    (hn : l.1.2 ≠ []) (ho : (clSplicedLeafNameEquiv hB hCL D l).1.1.2 ≠ [])
    (hp : GNode.parent (clSplicedLeafNameEquiv hB hCL D l).1.toNode ho ∉ S ∨
      GNode.parent (clSplicedLeafNameEquiv hB hCL D l).1.toNode ho = a) :
    l.1.2.getLast hn = (clSplicedLeafNameEquiv hB hCL D l).1.1.2.getLast ho := by
  obtain ⟨p, rfl⟩ := splicePieceNew_surjective (clSpliceBoundary hB hCL D) l
  change _ = ((spliceLeafEquiv (clSpliceBoundary hB hCL D) _).1).1.2.getLast _
  change (spliceLeafEquiv (clSpliceBoundary hB hCL D) _).1.1.2 ≠ [] at ho
  change GNode.parent (spliceLeafEquiv (clSpliceBoundary hB hCL D) _).1.toNode ho ∉ S ∨
    GNode.parent (spliceLeafEquiv (clSpliceBoundary hB hCL D) _).1.toNode ho = a at hp
  simp only [spliceLeafEquiv_piece] at ho hp ⊢
  cases p with
  | inl l => rfl
  | inr p =>
    exact cl_inside_port hB hCL D p.1 p.2.1 (TTree.leaves_subset_nodes _ p.2.2) ho hn hp

end WaveTurbulence.VineA
