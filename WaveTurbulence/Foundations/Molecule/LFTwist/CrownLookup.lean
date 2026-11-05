/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.CommonInflation
public import WaveTurbulence.Foundations.Molecule.BoundaryAddressAlgebra

/-! # Local code covariance on the actual lower-crown source subtree -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist
variable {w : ℕ} (S : Garden w) (P : CorePlacement S) (hS : S.IsPlain) (D : ReconstructionData S)

theorem branchLookup_exchange (b : GBranch S.tree) :
    branchLookup (twistReconstruction S P hS D)
      (exchangeAddress P.lower.1 (S.pair P.retained).1 P.keep b.1) = branchLookup D b.1 :=
  (congrArg (branchLookup (twistReconstruction S P hS D)) (coreBranchEquiv_address S P b).symm).trans
    ((branchLookup_twist S P hS D b).trans (branchLookup_branch D b).symm)

theorem leafLookup_exchange (hq : D.couple (pairOfLeaf S hS P.retained) = .triv) (l : GLeaf S.tree) :
    leafLookup (twistReconstruction S P hS D) (unitTwistGarden_plain S P hS)
      (exchangeAddress P.lower.1 (S.pair P.retained).1 P.keep l.1) = leafLookup D hS l.1 :=
  (congrArg (leafLookup (twistReconstruction S P hS D) (unitTwistGarden_plain S P hS))
    (coreLeafEquiv_address S P l).symm).trans
      ((leafLookup_twist_triv S P hS D hq l).trans (leafLookup_leaf D hS l).symm)

theorem ordinaryBranchSign_exchange (b : GBranch S.tree) (hb : b ≠ P.lower) :
    nodeSign (unitTwistGarden S P).sig
      (exchangeAddress P.lower.1 (S.pair P.retained).1 P.keep b.1) = nodeSign S.sig b.1 :=
  (congrArg (nodeSign (unitTwistGarden S P).sig) (coreBranchEquiv_address S P b).symm).trans
    (ordinaryBranchSign_twist S P b hb)

/-- The exact image of an entire child-rooted subtree. -/
theorem exchange_lower_child_root (a b : Address w) (keep i : Fin 3) :
    exchangeAddress a b keep (addrExt a [i]) = addrExt b [freeSwap keep i] := by
  simpa only [appendAddress, addrExt, List.append_nil] using exchangeAddress_lower_child a b keep i []

theorem exchange_respectsAt_lower_child (a b : Address w) (keep i : Fin 3) :
    RespectsAt (exchangeAddress a b keep) (addrExt a [i]) := by
  intro q
  have he : exchangeAddress a b keep (addrExt (addrExt a [i]) q) =
      addrExt (addrExt b [freeSwap keep i]) q := exchangeAddress_lower_child a b keep i q
  exact he.trans (congrArg (fun z => addrExt z q) (exchange_lower_child_root a b keep i).symm)

/-- Valid local crown branches are actual original source branches. -/
theorem crown_branch_mem (q : Path) (hq : q ∈ (lowerCrown S P.lower).branching) :
    (addrExt P.lower.1 q).2 ∈ (S.tree (addrExt P.lower.1 q).1).branching :=
  (Comb.subtree_branching_iff (Mole.spliceNodeSubtree_spec S P.lower.toNode) q).mp hq

theorem crown_leaf_mem (q : Path) (hq : q ∈ (lowerCrown S P.lower).leaves) :
    (addrExt P.lower.1 q).2 ∈ (S.tree (addrExt P.lower.1 q).1).leaves :=
  (Comb.subtree_leaves_iff (Mole.spliceNodeSubtree_spec S P.lower.toNode) q).mp hq

/-- Every nonroot branch of the crown is ordinary, so its sign is unchanged. -/
theorem crown_nonroot_branch_sign (q : Path) (hq : q ∈ (lowerCrown S P.lower).branching) (hne : q ≠ []) :
    nodeSign (unitTwistGarden S P).sig
      (exchangeAddress P.lower.1 (S.pair P.retained).1 P.keep (addrExt P.lower.1 q)) =
        nodeSign S.sig (addrExt P.lower.1 q) := by
  let b : GBranch S.tree := ⟨addrExt P.lower.1 q,crown_branch_mem S P q hq⟩
  apply ordinaryBranchSign_exchange S P b
  intro he
  have hp := congrArg (fun b : GBranch S.tree => b.1.2) he
  change P.lower.1.2 ++ q = P.lower.1.2 at hp
  have hl := congrArg List.length hp
  simp only [List.length_append] at hl
  exact hne (List.length_eq_zero_iff.mp (by omega))

end WaveTurbulence.LFTwist
