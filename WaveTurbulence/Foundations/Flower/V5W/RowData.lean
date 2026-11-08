/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5W.Defs
public import WaveTurbulence.Foundations.VineEst.RowSel.RowDataLemmas
public import WaveTurbulence.Foundations.VineEst.RowSel.RowDataLF

/-! # V5W-0: the row data of the pinned kernel form, read structurally

The selected regional factor `clLocalStarProductFW` and the multiplier `regionWeightFW` read the reconstruction data
through four new quantities: the incoherency indices `coupleIncoh`, `treeIncoh` (and `nodeRowIncoh` at a skeleton node)
and the root parent layers `coupleRootParents`, `treeRootParent`.  This file identifies them structurally:

* `coupleRootParents_zero/_one`, `treeRootParent_eq`: the root of a native row attached at a child `v.child j` of a
  skeleton branch has, in the reconstructed garden, the parent layer of the core of `v`
  (`ReconstructionData.core_child_position`);
* `nodeRowIncoh_branch`, `nodeRowIncoh_leaf`: the row of a branch node is its regular tree, the row of a leaf node is the
  regular couple of its source pair;
* `treeIncoh_LF`, `coupleIncoh_LF`: an LF construction keeps the incoherency of every ordinary row (rows unchanged by
  `tree_other`/`couple_other`, native layered rows unchanged by `native_tree_eq`/`native_couple_eq`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
noncomputable section
namespace WaveTurbulence.Flower.V5W
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.Links
  WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree

/- `parentLayer_coreChild`, `coupleRootParents_zero/_one`, `treeRootParent_eq`, `eq_or_pair_of_pairOfLeaf` are now on
main (416902c8, V5W-B: `VineEst/RowSel/RowDataLemmas.lean`, the same text in this namespace), imported above. -/
section Parents
variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer)

/-- The row of a branch node is its regular tree. -/
theorem nodeRowIncoh_branch (c : GBranch S.tree) :
    nodeRowIncoh D hS layer hLayer c.toNode = treeIncoh D hS layer hLayer c := by
  have h : ∃ c' : GBranch S.tree, c'.toNode = c.toNode := ⟨c, rfl⟩
  unfold nodeRowIncoh
  rw [dif_pos h]
  exact congrArg (treeIncoh D hS layer hLayer) (Mole.branch_toNode_injective h.choose_spec)

/-- The row of a leaf node is the regular couple of its source pair. -/
theorem nodeRowIncoh_leaf (l : GLeaf S.tree) :
    nodeRowIncoh D hS layer hLayer l.toNode = coupleIncoh D hS layer hLayer (pairOfLeaf S hS l) := by
  have hb : ¬ ∃ c : GBranch S.tree, c.toNode = l.toNode := fun ⟨c, hc⟩ => Mole.branch_toNode_ne_leaf c l hc
  have hq : ∃ pr : SourcePair S, (pr.firstLeaf hS).toNode = l.toNode ∨ (pr.secondLeaf hS).toNode = l.toNode := by
    refine ⟨pairOfLeaf S hS l, ?_⟩
    by_cases hs : nodeSign S.sig l.1 = 1
    · exact Or.inl (congrArg GLeaf.toNode (pairOfLeaf_sides_pos S hS l hs).1)
    · exact Or.inr (congrArg GLeaf.toNode (pairOfLeaf_sides_neg S hS l hs).2)
  unfold nodeRowIncoh
  rw [dif_neg hb, dif_pos hq]
  refine congrArg (coupleIncoh D hS layer hLayer) ?_
  rcases hq.choose_spec with h1 | h1
  · exact (pairOfLeaf_firstLeaf S hS _).symm.trans (congrArg (pairOfLeaf S hS) (Mole.leaf_toNode_injective h1))
  · exact (pairOfLeaf_secondLeaf S hS _).symm.trans (congrArg (pairOfLeaf S hS) (Mole.leaf_toNode_injective h1))

end Parents

/-! ## The incoherency of the ordinary rows under an LF construction

`treeIncoh_LF`, `coupleIncoh_LF` are now on main (416902c8, V5W-B: `VineEst/RowSel/RowDataLF.lean`), imported above. -/

end WaveTurbulence.Flower.V5W
