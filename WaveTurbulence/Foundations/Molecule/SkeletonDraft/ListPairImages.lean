/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Raw

/-! # Finite images of literal pair lists -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem list_map_toFinset {α β : Type*} [DecidableEq α] [DecidableEq β] (L : List α) (f : α → β) :
    (L.map f).toFinset = L.toFinset.image f := by
  ext x
  simp

end WaveTurbulence.Reg.Skeleton
