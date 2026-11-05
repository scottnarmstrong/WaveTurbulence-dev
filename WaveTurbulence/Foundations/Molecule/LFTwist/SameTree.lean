/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.LayeredUnit
public import WaveTurbulence.Foundations.Molecule.VineTwistPlacements

/-! # Both designated CL twist sites lie in the same source tree

TARGET lftwistprop L1483 uses per-tree layer-p counts. Generic placements
may cross tree indices; designated source CL placements do not.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Twist
variable {w : ℕ} {G : Garden w} (P : CorePlacement G)

/-- The designated internal retained position puts its paired endpoint's parent in the source block. -/
theorem paired_parent_selected {S : Finset (GBranch G.tree)} (hP : IsPlacementAt G S P.lower P) :
    GNode.parent (G.pair P.retained).toNode P.paired_nonroot ∈ S := by
  have hpos : Mole.dartPosition G (retainedLP G P) = P.keep.succ := by
    change (P.retained.1.2.getLast (retained_nonroot G P)).succ = P.keep.succ
    apply congrArg Fin.succ
    have hp : P.retained.1.2 = P.lower.1.2 ++ [P.keep] := congrArg (fun n : GNode G.tree => n.1.2) P.child
    simp only [hp,List.getLast_append_singleton]
  have hi := (hP.2 P.keep).mpr rfl
  obtain ⟨x,ha,hg,hxpos⟩ := (Mole.mem_internalPositions G).mp hi
  have hx : x = retainedLP G P := Mole.atom_position_injective G
    (Prod.ext (ha.trans (retained_parent G P).symm) (hxpos.trans hpos.symm))
  subst x
  exact hg.2

/-- The lower joint and the paired retained leaf of a designated CL vine
have the same original tree index, derived from the source block geometry. -/
theorem placement_same_tree {S : Finset (GBranch G.tree)} {a : GBranch G.tree}
    (hB : G.molecule.IsBlock S a P.lower) (hCL : Mole.CLParentPattern G S a P.lower)
    (hP : IsPlacementAt G S P.lower P) : P.lower.1.1 = (G.pair P.retained).1.1 := by
  have hd (v : GBranch G.tree) (hv : v ∈ S) :=
    Mole.block_one_root_descendants G hB hCL.1 hCL.2 hv
  have hb := hd P.lower hB.2.2.1
  have hp := hd (GNode.parent (G.pair P.retained).toNode P.paired_nonroot)
    (paired_parent_selected P hP)
  exact hb.1.symm.trans hp.1

/-- With the derived same-tree property, every transported branching node
keeps its original tree index. -/
theorem coreBranchEquiv_tree_index (he : P.lower.1.1 = (G.pair P.retained).1.1) (b : GBranch G.tree) :
    (coreBranchEquiv G P b).1.1 = b.1.1 := by
  rw [coreBranchEquiv_address]
  unfold exchangeAddress
  split
  · rename_i h
    exact he.symm.trans h.1.symm
  · split
    · rename_i h
      exact he.trans (congrArg Prod.fst h).symm
    · rfl

/-- Every transported leaf also keeps its original tree index. -/
theorem coreLeafEquiv_tree_index (he : P.lower.1.1 = (G.pair P.retained).1.1) (l : GLeaf G.tree) :
    (coreLeafEquiv G P l).1.1 = l.1.1 := by
  rw [coreLeafEquiv_address]
  unfold exchangeAddress
  split
  · rename_i h
    exact he.symm.trans h.1.symm
  · split
    · rename_i h
      exact he.trans (congrArg Prod.fst h).symm
    · rfl

end WaveTurbulence.LFTwist
