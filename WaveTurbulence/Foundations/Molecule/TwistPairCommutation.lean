/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistPairExceptionalLeaves

/-! # Actual unit twists at separated core CL vines commute

TARGET Definition twist: this compares literal gardens, including their
ordered trees, leaf pairing, marks and root signs. All geometric premises
for the second operations are derived from the original separated vines.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} {G : Garden w} {P Q : CorePlacement G}

/-- The leaf pairing follows both actual surgeries. -/
theorem CorePairData.pair (D : CorePairData G P Q) (l : GLeaf G.tree) :
    D.garden.pair (D.leaves l) = D.leaves (G.pair l) := by
  exact (unitTwistGarden_pair (unitTwistGarden G P) D.next (coreLeafEquiv G P l)).trans
    (congrArg (coreLeafEquiv (unitTwistGarden G P) D.next) (unitTwistGarden_pair G P l))

/-- Every original mark follows both actual surgeries. -/
theorem CorePairData.mark (D : CorePairData G P Q) (l : GLeaf G.tree) :
    D.garden.mark (D.leaves l) = G.mark l := by
  exact (unitTwistGarden_mark (unitTwistGarden G P) D.next (coreLeafEquiv G P l)).trans
    (unitTwistGarden_mark G P l)

/-- Two unit twists at separated source vines commute as literal gardens. -/
theorem CorePairData.garden_commute (D : CorePairData G P Q) : D.garden = D.swap.garden := by
  let e := D.swap.leaves.symm.trans D.leaves
  apply garden_eq_of_leaf_transport (H := D.garden) (K := D.swap.garden)
    rfl D.forest_commute e
  · intro m
    obtain ⟨l,rfl⟩ := D.swap.leaves.surjective m
    change (D.leaves (D.swap.leaves.symm (D.swap.leaves l))).1 = _
    exact (congrArg (fun l => (D.leaves l).1) (D.swap.leaves.symm_apply_apply l)).trans
      (D.leaf_commute l).symm
  · intro m
    obtain ⟨l,rfl⟩ := D.swap.leaves.surjective m
    change D.garden.pair (D.leaves (D.swap.leaves.symm (D.swap.leaves l))) =
      D.leaves (D.swap.leaves.symm (D.swap.garden.pair (D.swap.leaves l)))
    rw [D.swap.leaves.symm_apply_apply,D.pair,D.swap.pair,D.swap.leaves.symm_apply_apply]
  · intro m
    obtain ⟨l,rfl⟩ := D.swap.leaves.surjective m
    change D.garden.mark (D.leaves (D.swap.leaves.symm (D.swap.leaves l))) = _
    rw [D.swap.leaves.symm_apply_apply,D.mark,D.swap.mark]

end WaveTurbulence.Twist
