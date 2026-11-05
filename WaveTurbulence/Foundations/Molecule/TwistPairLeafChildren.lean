/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistPairBranchCommutation

/-! # Ordinary leaf children in both orders of separated twists -/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} {G : Garden w} {P Q : CorePlacement G}

/-- The ordered child-slot rule, written directly on actual branching-node equality. -/
@[expose] noncomputable def childSlot {H : Garden w} (R : CorePlacement H) (b : GBranch H.tree) (i : Fin 3) : Fin 3 :=
  if b = R.lower then freeSwap R.keep i else i

/-- The raw-address and actual-branch versions of the slot rule agree. -/
theorem childSlot_eq {H : Garden w} (R : CorePlacement H) (b : GBranch H.tree) (i : Fin 3) :
    childSlot R b i = exchangeChildSlot R.lower.1 R.keep b.1 i := by
  classical
  by_cases hb : b = R.lower
  · simp only [childSlot,exchangeChildSlot,hb,ite_true]
  · have hv : b.1 ≠ R.lower.1 := fun he => hb (Subtype.ext he)
    simp only [childSlot,exchangeChildSlot,hb,hv,ite_false]

/-- An ordinary leaf child follows the actual transported branch and its ordered slot. -/
theorem leaf_child_slot {H : Garden w} (R : CorePlacement H) {b : GBranch H.tree} {l : GLeaf H.tree} {i : Fin 3}
    (hc : l.toNode = b.child i) (hl : l ≠ H.pair R.retained) :
    (coreLeafEquiv H R l).toNode = (coreBranchEquiv H R b).child (childSlot R b i) := by
  exact (leaf_child_transport H R hc hl).trans (congrArg (coreBranchEquiv H R b).child (childSlot_eq R b i).symm)

/-- At the second site, the ordered slot test pulls back to the original lower atom. -/
theorem CorePairData.next_childSlot (D : CorePairData G P Q) (b : GBranch G.tree) (i : Fin 3) :
    childSlot D.next (coreBranchEquiv G P b) i = childSlot Q b i := by
  classical
  change (if coreBranchEquiv G P b = coreBranchEquiv G P Q.lower then freeSwap Q.keep i else i) = _
  simp only [(coreBranchEquiv G P).injective.eq_iff,childSlot]

/-- Avoiding an original exceptional partner is enough at the second actual site. -/
theorem CorePairData.not_next_pair (D : CorePairData G P Q) (l : GLeaf G.tree) (hl : l ≠ G.pair Q.retained) :
    coreLeafEquiv G P l ≠ (unitTwistGarden G P).pair D.next.retained := by
  intro he
  have hp := unitTwistGarden_pair G P Q.retained
  exact hl ((coreLeafEquiv G P).injective (he.trans hp))

/-- An ordinary original child follows two actual slot permutations. -/
theorem CorePairData.leaf_child (D : CorePairData G P Q) {b : GBranch G.tree} {l : GLeaf G.tree} {i : Fin 3}
    (hc : l.toNode = b.child i) (hp : l ≠ G.pair P.retained) (hq : l ≠ G.pair Q.retained) :
    (D.leaves l).toNode = (D.branches b).child (childSlot Q b (childSlot P b i)) := by
  have h₀ := leaf_child_slot P hc hp
  have h₁ := leaf_child_slot D.next h₀ (D.not_next_pair l hq)
  exact h₁.trans (congrArg (D.branches b).child (D.next_childSlot b (childSlot P b i)))

/-- The two child slot permutations commute because the lower atoms are distinct. -/
theorem CorePairData.childSlot_commute (D : CorePairData G P Q) (b : GBranch G.tree) (i : Fin 3) :
    childSlot Q b (childSlot P b i) = childSlot P b (childSlot Q b i) := by
  classical
  by_cases hp : b = P.lower
  · have hq : b ≠ Q.lower := fun he => D.lower_ne (hp.symm.trans he)
    simp only [childSlot,hp,D.lower_ne,ite_true,ite_false]
  · simp only [childSlot,hp,ite_false]

/-- Any leaf avoiding both exceptional partners has the same final actual address. -/
theorem CorePairData.ordinary_leaf_commute (D : CorePairData G P Q) (l : GLeaf G.tree)
    (hp : l ≠ G.pair P.retained) (hq : l ≠ G.pair Q.retained) :
    (D.swap.leaves l).1 = (D.leaves l).1 := by
  by_cases hn : l.1.2 = []
  · have rootval {H : Garden w} (R : CorePlacement H) (m : GLeaf H.tree) (hm : m.1.2 = []) :
        (coreLeafEquiv H R m).1 = m.1 := by
      rw [coreLeafEquiv_address]
      have hpre : ¬ R.lower.1.2 <+: m.1.2 := fun h => R.nonroot (List.eq_nil_of_prefix_nil (hm ▸ h))
      have he : m.1 ≠ (H.pair R.retained).1 := fun he =>
        R.paired_nonroot ((congrArg Prod.snd he).symm.trans hm)
      simp only [exchangeAddress,hpre,and_false,ite_false,he]
    have h₀ := rootval P l hn
    have h₁ := rootval D.next (coreLeafEquiv G P l) ((congrArg Prod.snd h₀).trans hn)
    have h₂ := rootval Q l hn
    have h₃ := rootval D.swap.next (coreLeafEquiv G Q l) ((congrArg Prod.snd h₂).trans hn)
    exact (h₃.trans h₂).trans (h₁.trans h₀).symm
  · let b := GNode.parent l.toNode hn
    let i := l.1.2.getLast hn
    have hc : l.toNode = b.child i := (Mole.parent_child_eq_node l.toNode hn).symm
    have h₀ := congrArg (fun n : GNode D.garden.tree => n.1) (D.leaf_child hc hp hq)
    have h₁ := congrArg (fun n : GNode D.swap.garden.tree => n.1) (D.swap.leaf_child hc hq hp)
    exact h₁.trans ((congrArg₂ (fun (v : Fin w × Path) (j : Fin 3) => (v.1,v.2 ++ [j]))
      (D.branch_commute b) (D.childSlot_commute b i).symm).trans h₀.symm)

end WaveTurbulence.Twist
