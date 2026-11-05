/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.InflationForest
public import WaveTurbulence.Foundations.Molecule.LFTwist.CommonFrames
public import WaveTurbulence.Foundations.Molecule.LFTwist.CrownInflation

/-! # Exact old/new reconstruction factorizations through one actual common forest -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist
variable {w : ℕ} (S : Garden w) (P : CorePlacement S) (hS : S.IsPlain) (D : ReconstructionData S)

@[expose] noncomputable def reconstructedCommonForest : Fin w → TTree :=
  inflateForestAt S.sig (branchLookup D) (leafLookup D hS) (commonForest S P.lower)

@[expose] noncomputable def reconstructedLowerHole : GLeaf (reconstructedCommonForest S P hS D) :=
  inflatedLeaf S.sig (branchLookup D) (leafLookup D hS) (commonForest S P.lower)
    (collapsedRoot S P.lower) (leafLookup_branch D hS P.lower)

theorem pairedHole_lookup_leaf (hq : D.couple (pairOfLeaf S hS P.retained) = .triv) :
    leafLookup D hS (pairedHole S P).1 = .leaf :=
  (leafLookup_leaf D hS (S.pair P.retained)).trans
    (leafTree_triv S hS D (S.pair P.retained) (by simpa only [pairOfLeaf_partner] using hq))

@[expose] noncomputable def reconstructedPairedHole
    (hq : D.couple (pairOfLeaf S hS P.retained) = .triv) : GLeaf (reconstructedCommonForest S P hS D) :=
  inflatedLeaf S.sig (branchLookup D) (leafLookup D hS) (commonForest S P.lower)
    (pairedHole S P) (pairedHole_lookup_leaf S P hS D hq)

/-- The exact original reconstruction inserts its inflated crown at the first hole. -/
theorem reconstruction_old_common_factor :
    D.forest hS = insertLeaf (reconstructedCommonForest S P hS D) (reconstructedLowerHole S P hS D)
      (inflateTreeAt S.sig (branchLookup D) (leafLookup D hS) (lowerCrown S P.lower) P.lower.1) := by
  calc
    _ = inflateForestAt S.sig (branchLookup D) (leafLookup D hS) S.tree :=
      funext (reconstruction_forest_eq_raw D hS)
    _ = inflateForestAt S.sig (branchLookup D) (leafLookup D hS)
        (insertLeaf (commonForest S P.lower) (collapsedRoot S P.lower) (lowerCrown S P.lower)) :=
      congrArg (inflateForestAt S.sig (branchLookup D) (leafLookup D hS)) (restore_commonForest S P.lower).symm
    _ = _ := inflateForest_insertLeaf S.sig (branchLookup D) (leafLookup D hS) (commonForest S P.lower)
      (collapsedRoot S P.lower) (leafLookup_branch D hS P.lower) (lowerCrown S P.lower)

theorem insertLeaf_congr_of_address {F H : Fin w → TTree} (hF : F = H) (l : GLeaf F) (m : GLeaf H)
    (ha : l.1 = m.1) (t u : TTree) (ht : t = u) : insertLeaf F l t = insertLeaf H m u := by
  subst H
  have he : l = m := Subtype.ext ha
  subst m
  subst u
  rfl

/-- The transported assignment inserts the switched inflated crown at the
second hole of exactly the same expanded common forest. -/
theorem reconstruction_new_common_factor (hnil : D.tree P.lower = .nil)
    (hq : D.couple (pairOfLeaf S hS P.retained) = .triv) :
    (twistReconstruction S P hS D).forest (unitTwistGarden_plain S P hS) =
      insertLeaf (reconstructedCommonForest S P hS D) (reconstructedPairedHole S P hS D hq)
        (switchFree P.keep (inflateTreeAt S.sig (branchLookup D) (leafLookup D hS)
          (lowerCrown S P.lower) P.lower.1)) := by
  let newD := twistReconstruction S P hS D
  let newX := branchLookup newD
  let newY := leafLookup newD (unitTwistGarden_plain S P hS)
  have hy : newY (pairedHole S P).1 = .leaf :=
    (congrArg newY (coreBranchEquiv_lower_val S P).symm).trans
      (leafLookup_branch newD (unitTwistGarden_plain S P hS) (coreBranchEquiv S P P.lower))
  let newCommon := inflateForestAt (unitTwistGarden S P).sig newX newY (commonForest S P.lower)
  let newHole := inflatedLeaf (unitTwistGarden S P).sig newX newY (commonForest S P.lower) (pairedHole S P) hy
  have hcommon : newCommon = reconstructedCommonForest S P hS D :=
    funext (commonForest_inflation_twist S P hS D hq)
  have hhole : newHole.1 = (reconstructedPairedHole S P hS D hq).1 :=
    common_rawSourcePosition_twist S P hS D (pairedHole S P).toNode
  have htree : (unitTwistGarden S P).tree =
      insertLeaf (commonForest S P.lower) (pairedHole S P) (switchFree P.keep (lowerCrown S P.lower)) := rfl
  calc
    _ = inflateForestAt (unitTwistGarden S P).sig newX newY (unitTwistGarden S P).tree :=
      funext (reconstruction_forest_eq_raw newD (unitTwistGarden_plain S P hS))
    _ = inflateForestAt (unitTwistGarden S P).sig newX newY
        (insertLeaf (commonForest S P.lower) (pairedHole S P) (switchFree P.keep (lowerCrown S P.lower))) :=
      congrArg (inflateForestAt (unitTwistGarden S P).sig newX newY) htree
    _ = insertLeaf newCommon newHole
        (inflateTreeAt (unitTwistGarden S P).sig newX newY (switchFree P.keep (lowerCrown S P.lower))
          (pairedHole S P).1) :=
      inflateForest_insertLeaf (unitTwistGarden S P).sig newX newY (commonForest S P.lower)
        (pairedHole S P) hy (switchFree P.keep (lowerCrown S P.lower))
    _ = _ := insertLeaf_congr_of_address hcommon newHole (reconstructedPairedHole S P hS D hq) hhole _ _
      (crown_inflation_twist S P hS D hnil hq)

end WaveTurbulence.LFTwist
