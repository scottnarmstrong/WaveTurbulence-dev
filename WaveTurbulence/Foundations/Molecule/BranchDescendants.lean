/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.CurrentBlockBridge
public import WaveTurbulence.Foundations.Molecule.CLBranchRealization

/-!
# Descendant exclusions in an actual CL vine

TARGET molecpl: no selected branching node can lie below an internal LP
leaf or an excluded child slot. These facts supply the incomparable
branches in scenarios (II-a) and (II-b).
-/

public section
namespace WaveTurbulence.Molecpl
open TTree
variable {w : ℕ} (G : Garden w)

/-- A leaf of the actual tree cannot be an ancestor of a branching node. -/
theorem leaf_not_ancestor_branch (l : GLeaf G.tree) (b : GBranch G.tree) :
    ¬ l.toNode.IsDesc b.toNode := by
  intro hd
  have hb : l.1.2 ∈ (G.tree l.1.1).branching :=
    Mole.branching_of_prefix_branching _ (hd.1.symm ▸ b.2) hd.2
  exact TTree.not_mem_branching_of_mem_leaves _ l.2 hb

/-- Every strict descendant lies below an actual child slot. -/
theorem strict_descendant_child {b : GBranch G.tree} {n : GNode G.tree}
    (hd : b.toNode.IsDesc n) (hne : b.toNode ≠ n) : ∃ i : Fin 3, (b.child i).IsDesc n := by
  obtain ⟨s,hs⟩ := hd.2
  cases s with
  | nil =>
    rw [List.append_nil] at hs
    exact (hne (Subtype.ext (Prod.ext hd.1 hs))).elim
  | cons i tail =>
    refine ⟨i,hd.1,tail,?_⟩
    simpa only [GBranch.child,GBranch.toNode,List.append_assoc,List.singleton_append] using hs

/-- A selected branch whose every internal child slot is a leaf has no strict selected descendants. -/
theorem cl_terminal_branch {S : Finset (GBranch G.tree)} {a b v : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : Mole.CLParentPattern G S a b) (hv : v ∈ S)
    (hleaf : ∀ i : Fin 3, i.succ ∈ Mole.internalPositions G S v →
      ∃ l : GLeaf G.tree, l.toNode = v.child i) :
    ∀ z ∈ S, v.toNode.IsDesc z.toNode → z = v := by
  intro z hz hd
  by_contra hne
  have hnodes : v.toNode ≠ z.toNode := fun he => hne (Mole.branch_toNode_injective he).symm
  obtain ⟨i,hi⟩ := strict_descendant_child G hd hnodes
  by_cases hint : i.succ ∈ Mole.internalPositions G S v
  · obtain ⟨l,hl⟩ := hleaf i hint
    exact leaf_not_ancestor_branch G l z (hl ▸ hi)
  · exact Mole.cl_excluded_child_no_descendant G hB hCL hv hz i hint hi

end WaveTurbulence.Molecpl
