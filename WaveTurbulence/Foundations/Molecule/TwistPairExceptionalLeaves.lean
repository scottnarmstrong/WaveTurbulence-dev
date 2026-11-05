/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistPairLeafChildren

/-! # The two exceptional partner leaves in separated-twist commutation -/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} {G : Garden w} {P Q : CorePlacement G}

/-- The two original exceptional partner leaves are different. -/
theorem CorePairData.paired_ne (D : CorePairData G P Q) : G.pair P.retained ≠ G.pair Q.retained := by
  intro he
  have hh := congrArg G.pair he
  simp only [G.pair_pair] at hh
  exact retained_ne_of_lower_ne G P Q D.lower_ne hh

/-- In the reverse order, the last surgery sends its exceptional partner to its lower site. -/
theorem CorePairData.last_paired_value (D : CorePairData G P Q) :
    (D.swap.leaves (G.pair P.retained)).1 = (coreBranchEquiv G Q P.lower).1 := by
  have hp := unitTwistGarden_pair G Q P.retained
  have he := congrArg (fun l => (coreLeafEquiv (unitTwistGarden G Q) D.swap.next l).1) hp
  exact he.symm.trans (coreLeafEquiv_paired_val (unitTwistGarden G Q) D.swap.next)

/-- The old lower parent remains outside that lower subtree after the other surgery. -/
theorem CorePairData.lower_parent_fixed_last (D : CorePairData G P Q) :
    (D.swap.branches (GNode.parent P.lower.toNode P.nonroot)).1 =
      (coreBranchEquiv G Q (GNode.parent P.lower.toNode P.nonroot)).1 := by
  have hp := branchParent_transport G Q P.lower P.nonroot D.lower_ne
  have hf := coreBranchEquiv_fixed_val (unitTwistGarden G Q) D.swap.next
    (GNode.parent (coreBranchEquiv G Q P.lower).toNode ((coreBranchEquiv_nonroot G Q P.lower).mpr P.nonroot))
    (lower_parent_outside (unitTwistGarden G Q) D.swap.next)
  have he := congrArg (fun b => (coreBranchEquiv (unitTwistGarden G Q) D.swap.next b).1) hp
  exact he.symm.trans (hf.trans (congrArg Subtype.val hp))

/-- The original exceptional partner has exactly the same actual final address in both orders. -/
theorem CorePairData.paired_leaf_commute (D : CorePairData G P Q) :
    (D.swap.leaves (G.pair P.retained)).1 = (D.leaves (G.pair P.retained)).1 := by
  let b := GNode.parent P.lower.toNode P.nonroot
  let i := P.lower.1.2.getLast P.nonroot
  have hb : (coreBranchEquiv G P b).1 = b.1 :=
    coreBranchEquiv_fixed_val G P b (lower_parent_outside G P)
  have hc : (coreLeafEquiv G P (G.pair P.retained)).toNode = (coreBranchEquiv G P b).child i := by
    apply Subtype.ext
    change (coreLeafEquiv G P (G.pair P.retained)).1 =
      ((coreBranchEquiv G P b).1.1,(coreBranchEquiv G P b).1.2 ++ [i])
    rw [coreLeafEquiv_paired_val,hb]
    exact (congrArg Subtype.val (Mole.parent_child_eq_node P.lower.toNode P.nonroot)).symm
  have h₁ := leaf_child_slot D.next hc (D.not_next_pair _ D.paired_ne)
  have h₁v := congrArg (fun n : GNode D.garden.tree => n.1) h₁
  have hparent : (D.branches b).1 = (coreBranchEquiv G Q b).1 :=
    (D.branch_commute b).symm.trans D.lower_parent_fixed_last
  have hslot := D.next_childSlot b i
  have hchild := branch_child_transport G Q (Mole.parent_child_eq_node P.lower.toNode P.nonroot).symm D.lower_ne
  have hchild' : (coreBranchEquiv G Q P.lower).toNode =
      (coreBranchEquiv G Q b).child (childSlot Q b i) :=
    hchild.trans (congrArg (coreBranchEquiv G Q b).child (childSlot_eq Q b i).symm)
  have hv : (D.leaves (G.pair P.retained)).1 = (coreBranchEquiv G Q P.lower).1 :=
    h₁v.trans ((congrArg₂ (fun (v : Fin w × Path) (j : Fin 3) => (v.1,v.2 ++ [j])) hparent hslot).trans
      (congrArg Subtype.val hchild').symm)
  exact D.last_paired_value.trans hv.symm

/-- Every actual leaf, including both exceptional partners, has the same final address. -/
theorem CorePairData.leaf_commute (D : CorePairData G P Q) (l : GLeaf G.tree) :
    (D.swap.leaves l).1 = (D.leaves l).1 := by
  by_cases hp : l = G.pair P.retained
  · subst l
    exact D.paired_leaf_commute
  · by_cases hq : l = G.pair Q.retained
    · subst l
      exact D.swap.paired_leaf_commute.symm
    · exact D.ordinary_leaf_commute l hp hq

end WaveTurbulence.Twist
