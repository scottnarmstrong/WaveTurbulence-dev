/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.LeafIncomparability
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.RawCoupleInsertion

/-! # Exact local typing data at a positive-negative source leaf pair -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

/-- The source A/couple insertion site, without unrelated global matching validity. -/
structure Raw.PairSite {w : ℕ} (R : Raw w) (x y : Address w) : Prop where
  leftLeaf : x.2 ∈ (R.tree x.1).leaves
  rightLeaf : y.2 ∈ (R.tree y.1).leaves
  positive : nodeSign R.sig x = 1
  negative : nodeSign R.sig y = -1
  pair_mem : (x,y) ∈ R.pairs

theorem Raw.PairSite.ne {w : ℕ} {R : Raw w} {x y : Address w} (h : R.PairSite x y) : x ≠ y := by
  intro he
  have hh := h.positive
  rw [he,h.negative] at hh
  contradiction

theorem Raw.PairSite.incomparable {w : ℕ} {R : Raw w} {x y : Address w} (h : R.PairSite x y) :
    (GLeaf.toNode (⟨x,h.leftLeaf⟩ : GLeaf R.tree)).Incomparable (GLeaf.toNode (⟨y,h.rightLeaf⟩ : GLeaf R.tree)) :=
  leaves_incomparable R.tree ⟨x,h.leftLeaf⟩ ⟨y,h.rightLeaf⟩
    (fun he => h.ne (congrArg (fun z : GLeaf R.tree => z.1) he).symm)

end WaveTurbulence.Reg.Skeleton
