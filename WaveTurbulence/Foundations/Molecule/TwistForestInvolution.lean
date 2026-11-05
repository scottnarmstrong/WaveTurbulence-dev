/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.CoreTwistCoordinates

/-! # The exact ordered-forest involution of a unit twist

TARGET twist and twistexplain: reverse the concrete exchange and switch
the same free children again. Both actual ordered forests are restored.
-/

public section
namespace WaveTurbulence.Twist
open TTree

/-- Collapsing a tree inserted at a leaf restores the common forest. -/
theorem collapse_insertLeaf {w : ℕ} (F : Fin w → TTree) (h : GLeaf F) (t : TTree) :
    Function.update (insertLeaf F h t) h.1.1
      (Comb.collapseAt (insertLeaf F h t h.1.1) h.1.2) = F := by
  funext j
  by_cases hj : j = h.1.1
  · subst j
    rw [Function.update_self,insertLeaf_at]
    unfold Comb.collapseAt
    rw [replaceAt_replaceAt]
    exact Comb.replaceAt_self ((subtree_leaf_iff _ _).mpr h.2)
  · rw [Function.update_of_ne hj]
    exact insertLeaf_other F h t j hj

variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The reverse operation has exactly the same common collapsed forest. -/
theorem reverse_commonForest : commonForest (unitTwistGarden G P) (reversePlacement G P).lower =
    commonForest G P.lower := by
  change Function.update (coreTwistForest G P) (coreBranchEquiv G P P.lower).1.1
    (Comb.collapseAt (coreTwistForest G P (coreBranchEquiv G P P.lower).1.1)
      (coreBranchEquiv G P P.lower).1.2) = _
  rw [coreBranchEquiv_lower_val]
  exact collapse_insertLeaf (commonForest G P.lower) (pairedHole G P) (switchFree P.keep (lowerCrown G P.lower))

/-- The reverse lower crown is the actual switched old crown. -/
theorem reverse_lowerCrown : lowerCrown (unitTwistGarden G P) (reversePlacement G P).lower =
    switchFree P.keep (lowerCrown G P.lower) := by
  have hs := Mole.spliceNodeSubtree_spec (unitTwistGarden G P) (reversePlacement G P).lower.toNode
  change Comb.subtree (coreTwistForest G P (coreBranchEquiv G P P.lower).1.1)
    (coreBranchEquiv G P P.lower).1.2 = some (lowerCrown (unitTwistGarden G P) (reversePlacement G P).lower) at hs
  rw [coreBranchEquiv_lower_val] at hs
  have ht := subtree_insertLeaf (commonForest G P.lower) (pairedHole G P) (switchFree P.keep (lowerCrown G P.lower))
  exact Option.some.inj (hs.symm.trans ht)

/-- The reverse paired insertion hole is at the original lower root address. -/
theorem reverse_pairedHole_val :
    (pairedHole (unitTwistGarden G P) (reversePlacement G P)).1 = P.lower.1 := by
  change ((unitTwistGarden G P).pair (coreLeafEquiv G P P.retained)).1 = _
  rw [unitTwistGarden_pair,coreLeafEquiv_paired_val]

/-- Performing the concrete unit twist twice restores the exact original ordered forest. -/
theorem coreTwistForest_involutive :
    coreTwistForest (unitTwistGarden G P) (reversePlacement G P) = G.tree := by
  change Function.update (commonForest (unitTwistGarden G P) (reversePlacement G P).lower)
    (pairedHole (unitTwistGarden G P) (reversePlacement G P)).1.1
    (Comb.replaceAt
      (commonForest (unitTwistGarden G P) (reversePlacement G P).lower
        (pairedHole (unitTwistGarden G P) (reversePlacement G P)).1.1)
      (pairedHole (unitTwistGarden G P) (reversePlacement G P)).1.2
      (switchFree P.keep (lowerCrown (unitTwistGarden G P) (reversePlacement G P).lower))) = _
  rw [reverse_pairedHole_val,reverse_commonForest,reverse_lowerCrown,switchFree_involutive]
  exact restore_commonForest G P.lower

end WaveTurbulence.Twist
