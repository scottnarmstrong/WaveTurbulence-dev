/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.TwistLookup
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CollapseBranchLabels
public import WaveTurbulence.Foundations.Molecule.TwistParents

/-! # Old and twisted reconstruction data inflate the exact same common forest

The two holes have literal leaf lookup values after the exceptional couple
is trivial. Every common branching node and every other common leaf retains
its original code/tree lookup. No outside-layer equality is assumed here.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist
variable {w : ℕ} (S : Garden w) (P : CorePlacement S) (hS : S.IsPlain) (D : ReconstructionData S)

theorem leafTree_triv (l : GLeaf S.tree) (hq : D.couple (pairOfLeaf S hS l) = .triv) :
    D.leafTree hS l = .leaf := by
  rw [ReconstructionData.leafTree, hq]
  simp only [RegCpl.trees, treeOfSign, ite_self]

/-- The branch contexts on the common forest are literally identical. -/
theorem common_branchLookup_twist (c : GBranch (commonForest S P.lower)) :
    branchLookup (twistReconstruction S P hS D) c.1 = branchLookup D c.1 := by
  have hb := (collapseNodeForest_branch_iff S.tree P.lower.toNode c.1).mp c.2
  let b : GBranch S.tree := ⟨c.1,hb.1⟩
  have hout : ¬ P.lower.toNode.IsDesc b.toNode := fun he => hb.2 ⟨he.1.symm,he.2⟩
  have hv : (coreBranchEquiv S P b).1 = c.1 := coreBranchEquiv_fixed_val S P b hout
  exact (congrArg (branchLookup (twistReconstruction S P hS D)) hv.symm).trans
    ((branchLookup_twist S P hS D b).trans (branchLookup_branch D b).symm)

/-- The common forest's leaf lookup values agree, including both exceptional holes. -/
theorem common_leafLookup_twist (hq : D.couple (pairOfLeaf S hS P.retained) = .triv)
    (c : GLeaf (commonForest S P.lower)) :
    leafLookup (twistReconstruction S P hS D) (unitTwistGarden_plain S P hS) c.1 = leafLookup D hS c.1 := by
  let newD := twistReconstruction S P hS D
  let hnew := unitTwistGarden_plain S P hS
  rcases (collapseNodeForest_leaf_iff S.tree P.lower.toNode c.1).mp c.2 with ⟨hl,hout⟩ | he
  · let l : GLeaf S.tree := ⟨c.1,hl⟩
    by_cases hp : l = S.pair P.retained
    · have hv : c.1 = (S.pair P.retained).1 := congrArg (fun z : GLeaf S.tree => z.1) hp
      have hq' : D.couple (pairOfLeaf S hS l) = .triv := by
        rw [hp, pairOfLeaf_partner]
        exact hq
      have hnewLeaf := leafLookup_branch newD hnew (coreBranchEquiv S P P.lower)
      have hcoord := coreBranchEquiv_lower_val S P
      exact (congrArg (leafLookup newD hnew) (hv.trans hcoord.symm)).trans
        (hnewLeaf.trans ((leafLookup_leaf D hS l).trans (leafTree_triv S hS D l hq')).symm)
    · have hLow : ¬ (l.1.1 = P.lower.1.1 ∧ P.lower.1.2 <+: l.1.2) := hout
      have hPair : l.1 ≠ (S.pair P.retained).1 := fun he => hp (Subtype.ext he)
      have hv : (coreLeafEquiv S P l).1 = l.1 := by
        rw [coreLeafEquiv_address]
        simp only [exchangeAddress, hLow, hPair, ite_false]
      exact (congrArg (leafLookup newD hnew) hv.symm).trans
        ((leafLookup_twist_triv S P hS D hq l).trans (leafLookup_leaf D hS l).symm)
  · have hq' : D.couple (pairOfLeaf S hS (S.pair P.retained)) = .triv := by
      simpa only [pairOfLeaf_partner] using hq
    have hnewLeaf : leafLookup newD hnew (coreLeafEquiv S P (S.pair P.retained)).1 = .leaf :=
      (leafLookup_twist_triv S P hS D hq (S.pair P.retained)).trans
        (leafTree_triv S hS D (S.pair P.retained) hq')
    have hv : c.1 = (coreLeafEquiv S P (S.pair P.retained)).1 :=
      he.trans (coreLeafEquiv_paired_val S P).symm
    exact (congrArg (leafLookup newD hnew) hv).trans
      (hnewLeaf.trans ((leafLookup_branch D hS P.lower).symm.trans (congrArg (leafLookup D hS) he.symm)))

/-- The entire common forest inflates identically on both sides of the skeleton twist. -/
theorem commonForest_inflation_twist (hq : D.couple (pairOfLeaf S hS P.retained) = .triv) (j : Fin w) :
    inflateTreeAt (unitTwistGarden S P).sig (branchLookup (twistReconstruction S P hS D))
      (leafLookup (twistReconstruction S P hS D) (unitTwistGarden_plain S P hS))
      (commonForest S P.lower j) (j,[]) =
    inflateTreeAt S.sig (branchLookup D) (leafLookup D hS) (commonForest S P.lower j) (j,[]) := by
  apply inflateTreeAt_map S.sig (unitTwistGarden S P).sig (branchLookup D) (leafLookup D hS)
    (branchLookup (twistReconstruction S P hS D))
    (leafLookup (twistReconstruction S P hS D) (unitTwistGarden_plain S P hS)) id
    (commonForest S P.lower j) (j,[]) (fun _ => rfl)
  · intro p hp
    simpa only [id_eq, addrExt, List.nil_append] using common_branchLookup_twist S P hS D ⟨(j,p),hp⟩
  · intro p hp
    simpa only [id_eq, addrExt, List.nil_append] using common_leafLookup_twist S P hS D hq ⟨(j,p),hp⟩
  · intro p hp
    rfl

end WaveTurbulence.LFTwist
