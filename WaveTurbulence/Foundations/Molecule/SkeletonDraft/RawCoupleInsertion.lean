/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.RawChainInsertion

/-! # Literal insertion of a regular couple at an actual positive-negative leaf pair -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

/-- Replace the two ordered leaf subtrees and their pair by the exact code trees and pairs. -/
noncomputable def Raw.insertCouple {w : ℕ} (R : Raw w) (x y : Address w) (Q : RegCpl) : Raw w :=
  let tree := Function.update R.tree x.1 ((R.tree x.1).setAt x.2 Q.trees.1)
  ⟨R.sig,Function.update tree y.1 ((tree y.1).setAt y.2 Q.trees.2),
    R.pairs.erase (x,y) ∪ (Q.pairsAt x y).toFinset⟩

theorem Raw.insertCouple_mini {w : ℕ} (R : Raw w) (x y : Address w) (c : MiniCplCode) :
    R.insertCouple x y (miniCoupleCode c) = R.opA x y c := by
  classical
  apply Raw.ext
  · rfl
  · simp only [Raw.insertCouple,Raw.opA,miniCoupleCode,RegCpl.trees]
    fin_cases c <;> rfl
  · simp [Raw.insertCouple,Raw.opA,miniCoupleCode,RegCpl.pairsAt]

end WaveTurbulence.Reg.Skeleton
