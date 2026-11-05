/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Raw

/-! # Finite union transport with one formerly empty replacement block -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem biUnion_image_single {ι α β : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq α] [DecidableEq β] (D : ι → Finset β) (E : ι → Finset α)
    (f : α → β) (b : ι) (hb : E b = ∅) (h : ∀ i, i ≠ b → D i = (E i).image f) :
    Finset.univ.biUnion D = (Finset.univ.biUnion E).image f ∪ D b := by
  ext x
  constructor
  · intro hx
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hx
    by_cases he : i = b
    · exact Finset.mem_union_right _ (he ▸ hi)
    · rw [h i he] at hi
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨y,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hy⟩,rfl⟩)
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hy
      have hn : i ≠ b := by
        intro he
        exact Finset.notMem_empty y (hb ▸ he ▸ hi)
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,by
        rw [h i hn]
        exact Finset.mem_image.mpr ⟨y,hi,rfl⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨b,Finset.mem_univ _,hx⟩

end WaveTurbulence.Reg.Skeleton
