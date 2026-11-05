/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourcePairSides

/-! # The two actual leaves of the canonical pair incident to a source leaf -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem pairOfLeaf_sides_pos {w : ℕ} (S : Garden w) (hS : S.IsPlain) (ℓ : GLeaf S.tree)
    (hs : nodeSign S.sig ℓ.1 = 1) :
    (pairOfLeaf S hS ℓ).firstLeaf hS = ℓ ∧
      (pairOfLeaf S hS ℓ).secondLeaf hS = S.pair ℓ := by
  constructor <;> apply Subtype.ext <;>
    simp only [SourcePair.firstLeaf,SourcePair.secondLeaf,pairOfLeaf,sourcePairAt,ite_eq_left hs]

theorem pairOfLeaf_sides_neg {w : ℕ} (S : Garden w) (hS : S.IsPlain) (ℓ : GLeaf S.tree)
    (hs : nodeSign S.sig ℓ.1 ≠ 1) :
    (pairOfLeaf S hS ℓ).firstLeaf hS = S.pair ℓ ∧
      (pairOfLeaf S hS ℓ).secondLeaf hS = ℓ := by
  constructor <;> apply Subtype.ext <;>
    simp only [SourcePair.firstLeaf,SourcePair.secondLeaf,pairOfLeaf,sourcePairAt,ite_eq_right hs]

end WaveTurbulence.Reg.Skeleton
