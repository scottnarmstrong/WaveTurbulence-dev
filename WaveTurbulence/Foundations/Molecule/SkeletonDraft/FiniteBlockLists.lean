/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Raw

/-! # Enumerating all finite replacement blocks as a literal list -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem length_univ_flatMap {ι α : Type*} [Fintype ι] [DecidableEq ι] (f : ι → List α) :
    (Finset.univ.toList.flatMap f).length = ∑ i, (f i).length := by
  rw [List.length_flatMap,Finset.sum_map_toList]

theorem toFinset_univ_flatMap {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (f : ι → List α) :
    (Finset.univ.toList.flatMap f).toFinset = Finset.univ.biUnion (fun i => (f i).toFinset) := by
  ext x
  simp

end WaveTurbulence.Reg.Skeleton
