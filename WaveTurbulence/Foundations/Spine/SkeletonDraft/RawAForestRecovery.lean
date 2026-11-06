/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.RawAPairRecovery
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.TwoRootRecovery
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourceMiniShapes

/-! # Exact forest inverse and full injectivity of a guarded raw A insertion -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem Raw.opA_forest_restore {w : ℕ} (R : Raw w) (hR : R.Valid) (x y : Address w)
    (k : MiniCplCode) (hp : (x,y) ∈ R.pairs) :
    let F := (R.opA x y k).tree
    let A := Function.update F x.1 (Comb.replaceAt (F x.1) x.2 .leaf)
    Function.update A y.1 (Comb.replaceAt (A y.1) y.2 .leaf) = R.tree := by
  have hv := hR.1 _ hp
  let ℓ : GLeaf R.tree := ⟨x,hv.1⟩
  let q : GLeaf R.tree := ⟨y,hv.2.1⟩
  have hn : q ≠ ℓ := fun he => valid_pair_ne R hR _ hp (congrArg (fun z : GLeaf R.tree => z.1) he).symm
  have hi := leaves_incomparable R.tree ℓ q hn
  have hs := twoRootReplacement_restore R.tree ℓ.toNode q.toNode hi
    (.node .leaf .leaf .leaf) (.node .leaf .leaf .leaf)
  rw [nodeSubtree_leaf R.tree ℓ,nodeSubtree_leaf R.tree q] at hs
  simp only [Raw.opA,setAt_eq_replaceAt]
  exact hs

theorem Raw.opA_tree_injective {w : ℕ} (R T : Raw w) (hR : R.Valid) (hT : T.Valid)
    (x y : Address w) (k : MiniCplCode) (hpR : (x,y) ∈ R.pairs) (hpT : (x,y) ∈ T.pairs)
    (he : R.opA x y k = T.opA x y k) : R.tree = T.tree := by
  have ht := congrArg (fun U : Raw w =>
    let A := Function.update U.tree x.1 (Comb.replaceAt (U.tree x.1) x.2 .leaf)
    Function.update A y.1 (Comb.replaceAt (A y.1) y.2 .leaf)) he
  exact (R.opA_forest_restore hR x y k hpR).symm.trans (ht.trans (T.opA_forest_restore hT x y k hpT))

/-- A guarded source A insertion is injective on the complete actual raw data. -/
theorem Raw.opA_injective_at {w : ℕ} (R T : Raw w) (hR : R.Valid) (hT : T.Valid)
    (x y : Address w) (k : MiniCplCode) (hpR : (x,y) ∈ R.pairs) (hpT : (x,y) ∈ T.pairs)
    (he : R.opA x y k = T.opA x y k) : R = T := by
  apply Raw.ext
  · have hs := congrArg Raw.sig he
    exact hs
  · exact Raw.opA_tree_injective R T hR hT x y k hpR hpT he
  · exact Raw.opA_pairs_injective R T hR hT x y k hpR hpT he

end WaveTurbulence.Reg.Skeleton
