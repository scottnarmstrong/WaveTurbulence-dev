/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistOuterReplacement

/-! # Actual lower boundary subtrees remain identical under their free-child switch

TARGET twistexplain (c,e): the two lower free subtrees are unchanged as
ordered trees and retain their signs; only their child slots are exchanged.
-/

public section
namespace WaveTurbulence.Twist
open TTree

/-- Extraction of each crown child commutes with the free-child permutation. -/
theorem subtree_switchFree_child (keep i : Fin 3) (t : TTree) :
    Comb.subtree (switchFree keep t) [freeSwap keep i] = Comb.subtree t [i] := by
  cases t with
  | leaf => simp [switchFree,Comb.subtree]
  | node l m r =>
    fin_cases keep <;> fin_cases i <;>
      simp [switchFree,freeSwap,Equiv.swap_apply_def,Comb.subtree]

variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The transported lower child carries exactly its original ordered subtree. -/
theorem lower_child_subtree (i : Fin 3) :
    Mole.spliceNodeSubtree (unitTwistGarden G P) ((coreBranchEquiv G P P.lower).child (freeSwap P.keep i)) =
      Mole.spliceNodeSubtree G (P.lower.child i) := by
  have hold := Mole.spliceNodeSubtree_spec G (P.lower.child i)
  change Comb.subtree (G.tree P.lower.1.1) (P.lower.1.2 ++ [i]) =
    some (Mole.spliceNodeSubtree G (P.lower.child i)) at hold
  have hroot : Comb.subtree (G.tree P.lower.1.1) P.lower.1.2 = some (lowerCrown G P.lower) :=
    Mole.spliceNodeSubtree_spec G P.lower.toNode
  rw [Comb.subtree_append,hroot] at hold
  have hnew := Mole.spliceNodeSubtree_spec (unitTwistGarden G P)
    ((coreBranchEquiv G P P.lower).child (freeSwap P.keep i))
  change Comb.subtree (coreTwistForest G P (coreBranchEquiv G P P.lower).1.1)
    ((coreBranchEquiv G P P.lower).1.2 ++ [freeSwap P.keep i]) =
      some (Mole.spliceNodeSubtree (unitTwistGarden G P) ((coreBranchEquiv G P P.lower).child (freeSwap P.keep i))) at hnew
  rw [coreBranchEquiv_lower_val,Comb.subtree_append] at hnew
  have hr : Comb.subtree (coreTwistForest G P (G.pair P.retained).1.1) (G.pair P.retained).1.2 =
      some (switchFree P.keep (lowerCrown G P.lower)) :=
    subtree_insertLeaf (commonForest G P.lower) (pairedHole G P) (switchFree P.keep (lowerCrown G P.lower))
  rw [hr] at hnew
  change Comb.subtree (switchFree P.keep (lowerCrown G P.lower)) [freeSwap P.keep i] =
    some (Mole.spliceNodeSubtree (unitTwistGarden G P) ((coreBranchEquiv G P P.lower).child (freeSwap P.keep i))) at hnew
  change Comb.subtree (lowerCrown G P.lower) [i] = some (Mole.spliceNodeSubtree G (P.lower.child i)) at hold
  exact Option.some.inj (hnew.symm.trans ((subtree_switchFree_child P.keep i (lowerCrown G P.lower)).trans hold))

end WaveTurbulence.Twist
