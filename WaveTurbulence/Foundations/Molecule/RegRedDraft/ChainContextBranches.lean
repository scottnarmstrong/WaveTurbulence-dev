/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ChainHoleReplacement
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReplacementBranches
public import WaveTurbulence.Foundations.RegStruct.ChainNodeBounds

/-! # Branches of a regular context persist under arbitrary filling of its lone hole -/

public section
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

theorem chain_branch_not_below_hole (X : RegChain) (ζ : ℤˣ) (q : Path)
    (hq : q ∈ (X.plug ζ .leaf).branching) : ¬ X.lonePath <+: q := by
  intro hp
  have he := leaf_prefix_node_eq (chain_lone_mem_leaves X ζ)
    (TTree.branching_subset_nodes _ hq) hp
  have hb : X.lonePath ∈ (X.plug ζ .leaf).branching := he.symm ▸ hq
  exact Comb.TreePath.not_mem_branching_of_mem_leaves _ (chain_lone_mem_leaves X ζ) hb

/-- Every internal context branch remains a genuine branch after its terminal
node is replaced by any actual subtree. -/
theorem chain_branching_subset_plug (X : RegChain) (ζ : ℤˣ) (h : TTree) :
    (X.plug ζ .leaf).branching ⊆ (X.plug ζ h).branching := by
  have he := branching_replaceAt_eq (plug_subtree_lonePath X ζ .leaf) h
  rw [replaceAt_plug_lonePath] at he
  intro q hq
  rw [he]
  exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hq,chain_branch_not_below_hole X ζ q hq⟩)

end WaveTurbulence.RegRed
