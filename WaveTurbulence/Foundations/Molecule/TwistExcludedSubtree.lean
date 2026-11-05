/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistBoundarySubtrees
public import WaveTurbulence.Foundations.Molecule.DisjointReplacement

/-! # The upper excluded boundary subtree is unchanged by a unit twist

TARGET twistexplain (c,e). The two changed positions lie inside the CL
incidence realization; the upper excluded subtree is disjoint from both.
-/

public section
namespace WaveTurbulence.Twist
open TTree

/-- A leaf ancestor of an actual node is that node itself. -/
theorem leaf_desc_node_eq {w : ℕ} {F : Fin w → TTree} (l : GLeaf F) (n : GNode F)
    (hd : l.toNode.IsDesc n) : l.toNode = n := by
  change l.1.1 = n.1.1 ∧ l.1.2 <+: n.1.2 at hd
  obtain ⟨r,hr⟩ := hd.2
  have hs := (subtree_leaf_iff (F l.1.1) l.1.2).mpr l.2
  have hm : r ∈ TTree.leaf.nodes := (Comb.subtree_nodes_iff hs r).mpr (by
    rw [hr]
    exact hd.1.symm ▸ n.2)
  have he : r = [] := Finset.mem_singleton.mp hm
  apply Subtype.ext
  change l.1 = n.1
  exact Prod.ext hd.1 (by simpa only [he,List.append_nil] using hr)

/-- Forest extraction at an incomparable same-tree address is unchanged by replacement. -/
theorem forestSubtree_replace_disjoint {w : ℕ} (F : Fin w → TTree) (a b : Fin w × Path)
    (hp : a.1 = b.1 → ¬ a.2 <+: b.2 ∧ ¬ b.2 <+: a.2) (t : TTree) :
    Comb.subtree (forestReplace F a t b.1) b.2 = Comb.subtree (F b.1) b.2 := by
  by_cases hi : b.1 = a.1
  · unfold forestReplace
    rw [hi,Function.update_self]
    exact Comb.subtree_replaceAt_disjoint _ _ _ (hp hi.symm).1 (hp hi.symm).2 t
  · rw [show forestReplace F a t b.1 = F b.1 from Function.update_of_ne hi _ _]

variable {w : ℕ} (G : Garden w) (P : CorePlacement G)
variable {S : Finset (GBranch G.tree)} {a : GBranch G.tree}

/-- The paired leaf u0 belongs to the actual internal incidence realization. -/
theorem placement_pair_in_realization (hB : G.molecule.IsBlock S a P.lower)
    (hP : IsPlacementAt G S P.lower P) :
    Mole.InIncidenceRealization G S (G.pair P.retained).toNode := by
  have ha : G.molecule.atom (retainedLP G P) = P.lower := retained_parent G P
  have hg : G.molecule.InGroup S (retainedLP G P) :=
    ⟨ha.symm ▸ hB.2.2.1,placement_paired_parent_mem G P hP⟩
  have hl : Mole.IsInternalLeaf G S P.retained :=
    ⟨P.unmarked,retained_nonroot G P,P.paired_nonroot,hg⟩
  exact (Mole.incidence_realization_leaf_pair G S P.retained).mpr
    ((Mole.leaf_incidence_realization_iff G S P.retained).mpr hl)

/-- The upper excluded child and the lower branching root are incomparable. -/
theorem excluded_lower_incomparable (hB : G.molecule.IsBlock S a P.lower)
    (hCL : Mole.CLParentPattern G S a P.lower) (D : Mole.CLSpliceSlots G S a P.lower) :
    (a.child D.excluded).Incomparable P.lower.toNode := by
  have hnot := Mole.cl_excluded_child_no_descendant G hB
    hCL hB.2.1 hB.2.2.1 D.excluded D.excluded_missing
  refine ⟨hnot,?_⟩
  intro hd
  have hlen := (Mole.cl_parent_strict_descendant G hB hCL).2
  have hh := hd.2.length_le
  have hle : (a.child D.excluded).1.2.length ≤ P.lower.1.2.length := by
    simp only [GBranch.child,List.length_append,List.length_singleton]
    omega
  have he := hd.2.eq_of_length_le hle
  have hn : P.lower.toNode = a.child D.excluded := Subtype.ext (Prod.ext hd.1 he)
  exact hnot (hn ▸ (show P.lower.toNode.IsDesc P.lower.toNode from ⟨rfl,List.prefix_refl _⟩))

/-- The upper excluded child and the actual leaf u0 are incomparable. -/
theorem excluded_pair_incomparable (hB : G.molecule.IsBlock S a P.lower)
    (hCL : Mole.CLParentPattern G S a P.lower) (hP : IsPlacementAt G S P.lower P)
    (D : Mole.CLSpliceSlots G S a P.lower) :
    (a.child D.excluded).Incomparable (G.pair P.retained).toNode := by
  have hr := (Mole.cl_node_realization_iff G hB hCL _).mp
    (placement_pair_in_realization G P hB hP)
  have hx := (Mole.cl_pruned_region_explicit G D.upper D.lower _).mp hr
  refine ⟨hx.2.1,?_⟩
  intro hd
  have he := leaf_desc_node_eq (G.pair P.retained) (a.child D.excluded) hd
  exact hx.2.1 (he ▸ (show (G.pair P.retained).toNode.IsDesc (G.pair P.retained).toNode from
    ⟨rfl,List.prefix_refl _⟩))

/-- The upper excluded rooted subtree is literally identical in the twisted forest. -/
theorem excluded_subtree_unchanged (hB : G.molecule.IsBlock S a P.lower)
    (hCL : Mole.CLParentPattern G S a P.lower) (hP : IsPlacementAt G S P.lower P)
    (D : Mole.CLSpliceSlots G S a P.lower) :
    Mole.spliceNodeSubtree (unitTwistGarden G P) ((coreBranchEquiv G P a).child D.excluded) =
      Mole.spliceNodeSubtree G (a.child D.excluded) := by
  have fa := selected_branch_fixed G P hB hCL hP hB.2.1 hB.2.2.2.1
  have hb := excluded_lower_incomparable G P hB hCL D
  have hp := excluded_pair_incomparable G P hB hCL hP D
  have hs := Mole.spliceNodeSubtree_spec (unitTwistGarden G P) ((coreBranchEquiv G P a).child D.excluded)
  change Comb.subtree (coreTwistForest G P (coreBranchEquiv G P a).1.1)
    ((coreBranchEquiv G P a).1.2 ++ [D.excluded]) = _ at hs
  rw [fa] at hs
  have he : Comb.subtree (coreTwistForest G P a.1.1) (a.1.2 ++ [D.excluded]) =
      Comb.subtree (G.tree a.1.1) (a.1.2 ++ [D.excluded]) := by
    change Comb.subtree
      (forestReplace (forestReplace G.tree P.lower.1 .leaf) (G.pair P.retained).1
        (switchFree P.keep (lowerCrown G P.lower)) a.1.1) (a.1.2 ++ [D.excluded]) = _
    exact (forestSubtree_replace_disjoint (forestReplace G.tree P.lower.1 .leaf)
      (G.pair P.retained).1 (a.1.1,a.1.2 ++ [D.excluded])
      (fun hi => ⟨fun h => hp.2 ⟨hi,h⟩,fun h => hp.1 ⟨hi.symm,h⟩⟩)
      (switchFree P.keep (lowerCrown G P.lower))).trans
        (forestSubtree_replace_disjoint G.tree P.lower.1 (a.1.1,a.1.2 ++ [D.excluded])
          (fun hi => ⟨fun h => hb.2 ⟨hi,h⟩,fun h => hb.1 ⟨hi.symm,h⟩⟩) .leaf)
  exact Option.some.inj (hs.symm.trans (he.trans (Mole.spliceNodeSubtree_spec G (a.child D.excluded))))

end WaveTurbulence.Twist
