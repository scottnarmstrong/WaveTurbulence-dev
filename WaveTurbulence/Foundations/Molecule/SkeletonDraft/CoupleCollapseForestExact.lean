/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.TwoRootRestoreInjective
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionRegularCouples
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.EraseCoupleForestFactorization

/-! # Collapsing one actual couple replacement leaves exactly the erased assignment forest -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem ReconstructionData.eraseCouple_collapse_tree {w : ℕ} {S G : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS G) (p : SourcePair S) :
    (collapseCoupleGarden (D.decoded_couple_isSubCouple hS hd p)).tree = (D.eraseCouple p).forest hS := by
  let E := D.eraseCouple p
  let A := inflatedPosition S D.tree (p.firstLeaf hS).toNode
  let B := inflatedPosition S D.tree (p.secondLeaf hS).toNode
  let a := D.decodedNode hS hd (p.firstLeaf hS).toNode
  let b := D.decodedNode hS hd (p.secondLeaf hS).toNode
  let h := D.decoded_couple_isSubCouple hS hd p
  have hforest : G.tree = ((E.raw hS).insertCouple A B (D.couple p)).tree :=
    (congrArg Raw.tree hd.2).symm.trans (congrArg Raw.tree (D.eraseCouple_raw hS p))
  have hrestore := (E.raw hS).insertCouple_tree_restore A B (D.eraseCouple_pairSite hS p) (D.couple p)
  have hc : (collapseCoupleGarden h).tree =
      (let F := G.tree
       let T := Function.update F A.1 (Comb.replaceAt (F A.1) A.2 .leaf)
       Function.update T B.1 (Comb.replaceAt (T B.1) B.2 .leaf)) := rfl
  exact hc.trans ((congrArg (fun F : Fin w → TTree =>
    let T := Function.update F A.1 (Comb.replaceAt (F A.1) A.2 .leaf)
    Function.update T B.1 (Comb.replaceAt (T B.1) B.2 .leaf)) hforest).trans hrestore)

end WaveTurbulence.Reg.Skeleton
