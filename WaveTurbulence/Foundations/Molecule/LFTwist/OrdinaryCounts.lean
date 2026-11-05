/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.NativeCoordinateEquiv

/-! # Source unchanged native layerings imply unchanged ordinary count contributions -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist Links RegRed
namespace LFConstruction
variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool}
    (h : LFConstruction s ε)

/-- Fixed core pre-layering preserves the entire original-tree core contribution. -/
theorem coreTopCount_eq (j : Fin w) :
    rawCoreTopCount LG s.data s.plain p j = rawCoreTopCount h.output h.data (s.chosen_plain ε) p j := by
  classical
  unfold rawCoreTopCount
  rw [← (s.branches ε).sum_comp]
  apply Finset.sum_congr rfl
  intro b _
  have hi : (h.data.coreBranch (s.chosen_plain ε) (s.branches ε b)).1.1 =
      (s.data.coreBranch s.plain b).1.1 :=
    (inflatedPosition_index (s.chosen ε) h.data.tree (s.branches ε b).toNode).trans
      ((s.branches_index ε b).trans (inflatedPosition_index s.skeleton s.data.tree b.toNode).symm)
  rw [hi,h.coreLayers b]
  rfl

/-- Ordinary regular-tree contributions agree in each original tree. -/
theorem ordinary_treeTopCount_eq (b : GBranch s.skeleton.tree) (hb : b ≠ s.placement.lower) (j : Fin w) :
    rawTreeTopCount LG s.data s.plain p b j =
      rawTreeTopCount h.output h.data (s.chosen_plain ε) p (s.branches ε b) j := by
  classical
  unfold rawTreeTopCount
  rw [← (h.treeBranches b hb).sum_comp]
  apply Finset.sum_congr rfl
  intro c _
  have hi : (chainContextBranch h.data (s.chosen_plain ε) (s.branches ε b) (h.treeBranches b hb c)).1.1 =
      (chainContextBranch s.data s.plain b c).1.1 :=
    (chainContextBranch_index h.data (s.chosen_plain ε) _ _).trans
      ((s.branches_index ε b).trans (chainContextBranch_index s.data s.plain b c).symm)
  rw [hi,h.ordinary_tree_branch_layer b hb c]

/-- Ordinary regular-couple contributions agree in each original tree. -/
theorem ordinary_coupleTopCount_eq (q : SourcePair s.skeleton) (hq : q ≠ s.exceptional) (j : Fin w) :
    rawCoupleTopCount LG s.data s.plain p q j =
      rawCoupleTopCount h.output h.data (s.chosen_plain ε) p (s.pairs ε q) j := by
  classical
  unfold rawCoupleTopCount
  rw [← (h.coupleBranches q hq).sum_comp]
  apply Finset.sum_congr rfl
  intro c _
  have hi : (coupleContextBranch h.data (s.chosen_plain ε) (s.pairs ε q) (h.coupleBranches q hq c)).1.1 =
      (coupleContextBranch s.data s.plain q c).1.1 := by
    rw [coupleContextBranch_address,coupleContextBranch_address]
    exact h.ordinary_couple_root_index q hq c.1.1
  rw [hi,h.ordinary_couple_branch_layer q hq c]

end LFConstruction
end WaveTurbulence.LFTwist
