/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionData

/-! # Literal replacement data are determined by their two code assignments -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.ext_tree_couple {w : ℕ} {S : Garden w} (D E : ReconstructionData S)
    (ht : D.tree = E.tree) (hc : D.couple = E.couple) : D = E := by
  cases D
  cases E
  cases ht
  cases hc
  rfl

end WaveTurbulence.Reg.Skeleton
