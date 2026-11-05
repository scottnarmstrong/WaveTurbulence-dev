/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.ReconstructionLookup
public import WaveTurbulence.Foundations.Molecule.LFTwist.TwistAttachments
public import WaveTurbulence.Foundations.Molecule.CoreBranchSigns

/-! # The exact raw reconstruction lookups under the skeleton unit twist -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist
variable {w : ℕ} (S : Garden w) (P : CorePlacement S) (hS : S.IsPlain) (D : ReconstructionData S)

theorem branchLookup_twist (b : GBranch S.tree) :
    branchLookup (twistReconstruction S P hS D) (coreBranchEquiv S P b).1 = D.tree b := by
  exact (branchLookup_branch (twistReconstruction S P hS D) (coreBranchEquiv S P b)).trans
    (transportReconstruction_tree hS (unitTwistGarden_plain S P hS) (coreBranchEquiv S P)
      (coreLeafEquiv S P) (fun l => (unitTwistGarden_pair S P l).symm) D b)

/-- Orientation normalization sends the exceptional pair to the actual new retained pair. -/
theorem twistReconstruction_couple_at_leaf (l : GLeaf S.tree) :
    (twistReconstruction S P hS D).couple
      (pairOfLeaf (unitTwistGarden S P) (unitTwistGarden_plain S P hS) (coreLeafEquiv S P l)) =
        D.couple (pairOfLeaf S hS l) := by
  have he := transportReconstruction_couple hS (unitTwistGarden_plain S P hS)
    (coreBranchEquiv S P) (coreLeafEquiv S P) (fun l => (unitTwistGarden_pair S P l).symm)
    D (pairOfLeaf S hS l)
  have hf := sourcePairEquiv_pairOfLeaf hS (unitTwistGarden_plain S P hS) (coreLeafEquiv S P)
    (fun l => (unitTwistGarden_pair S P l).symm) l
  exact (congrArg (twistReconstruction S P hS D).couple hf).symm.trans he

/-- All ordinary core branches retain their sign. -/
theorem ordinaryBranchSign_twist (b : GBranch S.tree) (hb : b ≠ P.lower) :
    nodeSign (unitTwistGarden S P).sig (coreBranchEquiv S P b).1 = nodeSign S.sig b.1 := by
  have hh := coreBranchEquiv_sign S P b
  rw [ite_eq_right hb] at hh
  exact hh

/-- Once the exceptional couple is trivial, every leaf replacement tree is
literally preserved by the source leaf bijection, even at the sign-flipped pair. -/
theorem leafLookup_twist_triv (hq : D.couple (pairOfLeaf S hS P.retained) = .triv) (l : GLeaf S.tree) :
    leafLookup (twistReconstruction S P hS D) (unitTwistGarden_plain S P hS) (coreLeafEquiv S P l).1 =
      D.leafTree hS l := by
  apply (leafLookup_leaf (twistReconstruction S P hS D)
    (unitTwistGarden_plain S P hS) (coreLeafEquiv S P l)).trans
  change treeOfSign ((twistReconstruction S P hS D).couple
    (pairOfLeaf (unitTwistGarden S P) (unitTwistGarden_plain S P hS) (coreLeafEquiv S P l))).trees
      (nodeSign (unitTwistGarden S P).sig (coreLeafEquiv S P l).1) =
    treeOfSign (D.couple (pairOfLeaf S hS l)).trees (nodeSign S.sig l.1)
  rw [twistReconstruction_couple_at_leaf S P hS D l]
  by_cases he : l = P.retained ∨ l = S.pair P.retained
  · have hq' : D.couple (pairOfLeaf S hS l) = .triv := by
      rcases he with rfl | rfl
      · exact hq
      · simpa only [pairOfLeaf_partner] using hq
    rw [hq']
    simp only [RegCpl.trees, treeOfSign, ite_self]
  · have hs : nodeSign (unitTwistGarden S P).sig (coreLeafEquiv S P l).1 = nodeSign S.sig l.1 := by
      apply (coreLeafEquiv_sign S P l).trans
      rw [coreLeafMultiplier, ite_eq_right he, one_mul]
      rfl
    rw [hs]

end WaveTurbulence.LFTwist
