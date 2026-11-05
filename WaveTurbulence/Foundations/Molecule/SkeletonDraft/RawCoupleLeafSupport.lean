/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.RawCoupleGraftForest
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.GraftPairLeafSupport
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.RawPairEndpointExclusion

/-! # Every old or inserted pair endpoint is a leaf of a valid typed couple graft -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem Raw.insertCouple_pair_endpoints {w : ℕ} (R : Raw w) (hR : R.Valid)
    (x y : Address w) (h : R.PairSite x y) (Q : RegCpl) (p : Pair w)
    (hp : p ∈ (R.insertCouple x y Q).pairs) :
    p.1.2 ∈ ((R.insertCouple x y Q).tree p.1.1).leaves ∧
      p.2.2 ∈ ((R.insertCouple x y Q).tree p.2.1).leaves := by
  classical
  let ℓ : GLeaf R.tree := ⟨x,h.leftLeaf⟩
  let q : GLeaf R.tree := ⟨y,h.rightLeaf⟩
  have hne : q ≠ ℓ := fun he => h.ne (congrArg (fun z : GLeaf R.tree => z.1) he).symm
  rw [R.insertCouple_forest x y h Q]
  change p ∈ R.pairs.erase (x,y) ∪ (Q.pairsAt x y).toFinset at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · obtain ⟨hn,hp⟩ := Finset.mem_erase.mp hp
    have hv := (hR.1 p hp)
    have he := hR.pair_ne_endpoints h p hp hn
    let u : GLeaf R.tree := ⟨p.1,hv.1⟩
    let v : GLeaf R.tree := ⟨p.2,hv.2.1⟩
    exact ⟨graftPair_old_leaf R.tree ℓ q hne Q.trees.1 Q.trees.2 u
      (fun hh => he.1 (congrArg Subtype.val hh)) (fun hh => he.2.1 (congrArg Subtype.val hh)),
      graftPair_old_leaf R.tree ℓ q hne Q.trees.1 Q.trees.2 v
      (fun hh => he.2.2.1 (congrArg Subtype.val hh)) (fun hh => he.2.2.2 (congrArg Subtype.val hh))⟩
  · have hv := couple_pair_endpoint_leaves Q x y p (List.mem_toFinset.mp hp)
    exact ⟨graftPair_inserted_leaf R.tree ℓ q hne Q.trees.1 Q.trees.2 p.1 hv.1,
      graftPair_inserted_leaf R.tree ℓ q hne Q.trees.1 Q.trees.2 p.2 hv.2⟩

end WaveTurbulence.Reg.Skeleton
