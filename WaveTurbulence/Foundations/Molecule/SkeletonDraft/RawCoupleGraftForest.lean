/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.RawCoupleIdentity
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.GraftPairLeafEquiv

/-! # Literal couple insertion has the exact two-leaf graft forest -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem Raw.insertCouple_forest {w : ℕ} (R : Raw w) (x y : Address w)
    (h : R.PairSite x y) (Q : RegCpl) :
    (R.insertCouple x y Q).tree = Comb.graftLeafPairForest R.tree
      ⟨x,h.leftLeaf⟩ ⟨y,h.rightLeaf⟩
      (fun he => h.ne (congrArg (fun z : GLeaf R.tree => z.1) he).symm) Q.trees.1 Q.trees.2 := by
  simp only [Raw.insertCouple,Comb.graftLeafPairForest,Comb.graftLeafForest,
    Comb.graftLeafForest_other,setAt_eq_replaceAt]

theorem Raw.insertCouple_order {w : ℕ} (R : Raw w) (x y : Address w)
    (h : R.PairSite x y) (Q : RegCpl) : (R.insertCouple x y Q).order = R.order + Q.size := by
  have ht := congrArg (fun tree : Fin w → TTree => ∑ j, (tree j).order)
    (R.insertCouple_forest x y h Q)
  have hg := Comb.graftLeafPairForest_order R.tree (⟨x,h.leftLeaf⟩ : GLeaf R.tree)
    (⟨y,h.rightLeaf⟩ : GLeaf R.tree)
    (fun he => h.ne (congrArg (fun z : GLeaf R.tree => z.1) he).symm) Q.trees.1 Q.trees.2
  have he := code_trees_order Q
  change (∑ j, ((R.insertCouple x y Q).tree j).order) = (∑ j, (R.tree j).order) + Q.size
  omega

end WaveTurbulence.Reg.Skeleton
