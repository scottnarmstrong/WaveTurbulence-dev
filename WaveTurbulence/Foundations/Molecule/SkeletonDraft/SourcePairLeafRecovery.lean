/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourcePairSides

/-! # Recovering either actual leaf from its canonical oriented source pair -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem pairOfLeaf_first_of_positive {w : ℕ} (S : Garden w) (hS : S.IsPlain) (ℓ : GLeaf S.tree)
    (hℓ : nodeSign S.sig ℓ.1 = 1) : (pairOfLeaf S hS ℓ).firstLeaf hS = ℓ := by
  apply Subtype.ext
  change (sourcePairAt S ℓ).1 = ℓ.1
  rw [sourcePairAt,ite_eq_left hℓ]

theorem pairOfLeaf_second_of_negative {w : ℕ} (S : Garden w) (hS : S.IsPlain) (ℓ : GLeaf S.tree)
    (hℓ : nodeSign S.sig ℓ.1 ≠ 1) : (pairOfLeaf S hS ℓ).secondLeaf hS = ℓ := by
  apply Subtype.ext
  change (sourcePairAt S ℓ).2 = ℓ.1
  rw [sourcePairAt,ite_eq_right hℓ]

end WaveTurbulence.Reg.Skeleton
