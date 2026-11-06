/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.LeafIncomparability
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.TwoRootReplacementShapes
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ForwardBShape

/-! # The two literal corollas created by a guarded raw A expansion -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem Raw.opA_subtrees {w : ℕ} (R : Raw w) (hR : R.Valid) (x y : Address w)
    (k : MiniCplCode) (hp : (x,y) ∈ R.pairs) :
    Comb.subtree ((R.opA x y k).tree x.1) x.2 = some (.node .leaf .leaf .leaf) ∧
      Comb.subtree ((R.opA x y k).tree y.1) y.2 = some (.node .leaf .leaf .leaf) := by
  have hv := hR.1 _ hp
  let ℓ : GLeaf R.tree := ⟨x,hv.1⟩
  let q : GLeaf R.tree := ⟨y,hv.2.1⟩
  have hn : q ≠ ℓ := fun he => valid_pair_ne R hR _ hp (congrArg (fun z : GLeaf R.tree => z.1) he).symm
  have hi := leaves_incomparable R.tree ℓ q hn
  have hs := twoRootReplacement_subtrees R.tree ℓ.toNode q.toNode hi
    (.node .leaf .leaf .leaf) (.node .leaf .leaf .leaf)
  simp only [Raw.opA,setAt_eq_replaceAt]
  exact hs

theorem branches_of_raw_opA {w : ℕ} (R : Raw w) (hR : R.Valid) (G : Garden w)
    (x y : Address w) (k : MiniCplCode) (hp : (x,y) ∈ R.pairs)
    (he : rawOfGarden G = R.opA x y k) :
    ∃ b c : GBranch G.tree, b.1 = x ∧ c.1 = y := by
  have ht : G.tree = (R.opA x y k).tree := congrArg Raw.tree he
  have hs := R.opA_subtrees hR x y k hp
  rw [← ht] at hs
  let b : GBranch G.tree := branchOfExtraction G.tree x (fun _ => .leaf) hs.1
  let c : GBranch G.tree := branchOfExtraction G.tree y (fun _ => .leaf) hs.2
  exact ⟨b,c,rfl,rfl⟩

end WaveTurbulence.Reg.Skeleton
