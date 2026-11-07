/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.MixedPairEnumerations
public import WaveTurbulence.Foundations.FinalCount.Algorithm.VertexLabels
public import WaveTurbulence.Foundations.FinalCount.Algorithm.TableRealization
import Mathlib.Tactic

/-! # The eight literal mixed-degree source figures -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def d34oneRealization (M : Molecule V D)
    {a b c d p : V} (hab : a ≠ b)
    (hnd : ([a,b,c,d,p] : List V).Nodup) (hmem : ∀ v ∈ ([a,b,c,d,p] : List V),v ∈ M.atoms)
    (hda : M.deg a = 3) (hdb : M.deg b = 4) (data : MixedPairEdges M a b 2 1 2)
    (hl0 : data.left.neighbor 0 = c)
    (hr0 : data.right.neighbor 0 = d)
    (hr1 : data.right.neighbor 1 = p)
    : AppbRealization M AppbPatternKind.d34one.pattern := by
  classical
  let f := vertexLabels [a,b,c,d,p] a
  have hV : AppbPatternKind.d34one.pattern.vertices = Icc 1 5 := by decide
  have hf : Set.InjOn f (AppbPatternKind.d34one.pattern.vertices : Set ℕ) := by
    rw [hV]
    exact vertexLabels_injective a hnd
  have hm : ∀ i ∈ AppbPatternKind.d34one.pattern.vertices,f i ∈ M.atoms := by
    intro i hi
    rw [hV] at hi
    exact hmem _ (vertexLabels_mem a hi)
  apply realizationOfTable M AppbPatternKind.d34one.pattern f hf hm data.enumeration
    (data.enumeration_injective hab) data.enumeration_outgoing ?_ (by decide) ?_
  · intro i
    have hh := data.d34_endpoints i
    fin_cases i <;> simpa [f,vertexLabels,AppbPatternKind.pattern,hl0,hr0,hr1] using hh
  · intro i hi
    have hi' : i = 1 ∨ i = 2 := by
      simpa only [AppbPatternKind.pattern,mem_insert,mem_singleton] using hi
    rcases hi' with rfl | rfl
    · exact hda
    · exact hdb

noncomputable def d34twoRealization (M : Molecule V D)
    {a b c d : V} (hab : a ≠ b)
    (hnd : ([a,b,c,d] : List V).Nodup) (hmem : ∀ v ∈ ([a,b,c,d] : List V),v ∈ M.atoms)
    (hda : M.deg a = 3) (hdb : M.deg b = 4) (data : MixedPairEdges M a b 2 1 2)
    (hl0 : data.left.neighbor 0 = c)
    (hr0 : data.right.neighbor 0 = c)
    (hr1 : data.right.neighbor 1 = d)
    : AppbRealization M AppbPatternKind.d34two.pattern := by
  classical
  let f := vertexLabels [a,b,c,d] a
  have hV : AppbPatternKind.d34two.pattern.vertices = Icc 1 4 := by decide
  have hf : Set.InjOn f (AppbPatternKind.d34two.pattern.vertices : Set ℕ) := by
    rw [hV]
    exact vertexLabels_injective a hnd
  have hm : ∀ i ∈ AppbPatternKind.d34two.pattern.vertices,f i ∈ M.atoms := by
    intro i hi
    rw [hV] at hi
    exact hmem _ (vertexLabels_mem a hi)
  apply realizationOfTable M AppbPatternKind.d34two.pattern f hf hm data.enumeration
    (data.enumeration_injective hab) data.enumeration_outgoing ?_ (by decide) ?_
  · intro i
    have hh := data.d34_endpoints i
    fin_cases i <;> simpa [f,vertexLabels,AppbPatternKind.pattern,hl0,hr0,hr1] using hh
  · intro i hi
    have hi' : i = 1 ∨ i = 2 := by
      simpa only [AppbPatternKind.pattern,mem_insert,mem_singleton] using hi
    rcases hi' with rfl | rfl
    · exact hda
    · exact hdb

noncomputable def d34threeRealization (M : Molecule V D)
    {a b c d : V} (hab : a ≠ b)
    (hnd : ([a,b,c,d] : List V).Nodup) (hmem : ∀ v ∈ ([a,b,c,d] : List V),v ∈ M.atoms)
    (hda : M.deg a = 3) (hdb : M.deg b = 4) (data : MixedPairEdges M a b 2 1 2)
    (hl0 : data.left.neighbor 0 = c)
    (hr0 : data.right.neighbor 0 = d)
    (hr1 : data.right.neighbor 1 = d)
    : AppbRealization M AppbPatternKind.d34three.pattern := by
  classical
  let f := vertexLabels [a,b,c,d] a
  have hV : AppbPatternKind.d34three.pattern.vertices = Icc 1 4 := by decide
  have hf : Set.InjOn f (AppbPatternKind.d34three.pattern.vertices : Set ℕ) := by
    rw [hV]
    exact vertexLabels_injective a hnd
  have hm : ∀ i ∈ AppbPatternKind.d34three.pattern.vertices,f i ∈ M.atoms := by
    intro i hi
    rw [hV] at hi
    exact hmem _ (vertexLabels_mem a hi)
  apply realizationOfTable M AppbPatternKind.d34three.pattern f hf hm data.enumeration
    (data.enumeration_injective hab) data.enumeration_outgoing ?_ (by decide) ?_
  · intro i
    have hh := data.d34_endpoints i
    fin_cases i <;> simpa [f,vertexLabels,AppbPatternKind.pattern,hl0,hr0,hr1] using hh
  · intro i hi
    have hi' : i = 1 ∨ i = 2 := by
      simpa only [AppbPatternKind.pattern,mem_insert,mem_singleton] using hi
    rcases hi' with rfl | rfl
    · exact hda
    · exact hdb

noncomputable def d34fourRealization (M : Molecule V D)
    {a b c : V} (hab : a ≠ b)
    (hnd : ([a,b,c] : List V).Nodup) (hmem : ∀ v ∈ ([a,b,c] : List V),v ∈ M.atoms)
    (hda : M.deg a = 3) (hdb : M.deg b = 4) (data : MixedPairEdges M a b 2 1 2)
    (hl0 : data.left.neighbor 0 = c)
    (hr0 : data.right.neighbor 0 = c)
    (hr1 : data.right.neighbor 1 = c)
    : AppbRealization M AppbPatternKind.d34four.pattern := by
  classical
  let f := vertexLabels [a,b,c] a
  have hV : AppbPatternKind.d34four.pattern.vertices = Icc 1 3 := by decide
  have hf : Set.InjOn f (AppbPatternKind.d34four.pattern.vertices : Set ℕ) := by
    rw [hV]
    exact vertexLabels_injective a hnd
  have hm : ∀ i ∈ AppbPatternKind.d34four.pattern.vertices,f i ∈ M.atoms := by
    intro i hi
    rw [hV] at hi
    exact hmem _ (vertexLabels_mem a hi)
  apply realizationOfTable M AppbPatternKind.d34four.pattern f hf hm data.enumeration
    (data.enumeration_injective hab) data.enumeration_outgoing ?_ (by decide) ?_
  · intro i
    have hh := data.d34_endpoints i
    fin_cases i <;> simpa [f,vertexLabels,AppbPatternKind.pattern,hl0,hr0,hr1] using hh
  · intro i hi
    have hi' : i = 1 ∨ i = 2 := by
      simpa only [AppbPatternKind.pattern,mem_insert,mem_singleton] using hi
    rcases hi' with rfl | rfl
    · exact hda
    · exact hdb

noncomputable def s32oneRealization (M : Molecule V D)
    {a b c d : V} (hab : a ≠ b)
    (hnd : ([a,b,c,d] : List V).Nodup) (hmem : ∀ v ∈ ([a,b,c,d] : List V),v ∈ M.atoms)
    (hda : M.deg a = 3) (hdb : M.deg b = 2) (data : MixedPairEdges M a b 1 2 1)
    (hl0 : data.left.neighbor 0 = c)
    (hl1 : data.left.neighbor 1 = c)
    (hr0 : data.right.neighbor 0 = d)
    : AppbRealization M AppbPatternKind.s32one.pattern := by
  classical
  let f := vertexLabels [a,b,c,d] a
  have hV : AppbPatternKind.s32one.pattern.vertices = Icc 1 4 := by decide
  have hf : Set.InjOn f (AppbPatternKind.s32one.pattern.vertices : Set ℕ) := by
    rw [hV]
    exact vertexLabels_injective a hnd
  have hm : ∀ i ∈ AppbPatternKind.s32one.pattern.vertices,f i ∈ M.atoms := by
    intro i hi
    rw [hV] at hi
    exact hmem _ (vertexLabels_mem a hi)
  apply realizationOfTable M AppbPatternKind.s32one.pattern f hf hm data.s32Enumeration
    (data.s32Enumeration_injective hab) data.s32Enumeration_outgoing ?_ (by decide) ?_
  · intro i
    have hh := data.s32_endpoints i
    fin_cases i <;> simpa [f,vertexLabels,AppbPatternKind.pattern,hl0,hl1,hr0] using hh
  · intro i hi
    have hi' : i = 1 ∨ i = 2 := by
      simpa only [AppbPatternKind.pattern,mem_insert,mem_singleton] using hi
    rcases hi' with rfl | rfl
    · exact hda
    · exact hdb

noncomputable def s32twoRealization (M : Molecule V D)
    {a b c : V} (hab : a ≠ b)
    (hnd : ([a,b,c] : List V).Nodup) (hmem : ∀ v ∈ ([a,b,c] : List V),v ∈ M.atoms)
    (hda : M.deg a = 3) (hdb : M.deg b = 2) (data : MixedPairEdges M a b 1 2 1)
    (hl0 : data.left.neighbor 0 = c)
    (hl1 : data.left.neighbor 1 = c)
    (hr0 : data.right.neighbor 0 = c)
    : AppbRealization M AppbPatternKind.s32two.pattern := by
  classical
  let f := vertexLabels [a,b,c] a
  have hV : AppbPatternKind.s32two.pattern.vertices = Icc 1 3 := by decide
  have hf : Set.InjOn f (AppbPatternKind.s32two.pattern.vertices : Set ℕ) := by
    rw [hV]
    exact vertexLabels_injective a hnd
  have hm : ∀ i ∈ AppbPatternKind.s32two.pattern.vertices,f i ∈ M.atoms := by
    intro i hi
    rw [hV] at hi
    exact hmem _ (vertexLabels_mem a hi)
  apply realizationOfTable M AppbPatternKind.s32two.pattern f hf hm data.s32Enumeration
    (data.s32Enumeration_injective hab) data.s32Enumeration_outgoing ?_ (by decide) ?_
  · intro i
    have hh := data.s32_endpoints i
    fin_cases i <;> simpa [f,vertexLabels,AppbPatternKind.pattern,hl0,hl1,hr0] using hh
  · intro i hi
    have hi' : i = 1 ∨ i = 2 := by
      simpa only [AppbPatternKind.pattern,mem_insert,mem_singleton] using hi
    rcases hi' with rfl | rfl
    · exact hda
    · exact hdb

noncomputable def s32threeRealization (M : Molecule V D)
    {a b c d p : V} (hab : a ≠ b)
    (hnd : ([a,b,c,d,p] : List V).Nodup) (hmem : ∀ v ∈ ([a,b,c,d,p] : List V),v ∈ M.atoms)
    (hda : M.deg a = 3) (hdb : M.deg b = 2) (data : MixedPairEdges M a b 1 2 1)
    (hl0 : data.left.neighbor 0 = c)
    (hl1 : data.left.neighbor 1 = d)
    (hr0 : data.right.neighbor 0 = p)
    : AppbRealization M AppbPatternKind.s32three.pattern := by
  classical
  let f := vertexLabels [a,b,c,d,p] a
  have hV : AppbPatternKind.s32three.pattern.vertices = Icc 1 5 := by decide
  have hf : Set.InjOn f (AppbPatternKind.s32three.pattern.vertices : Set ℕ) := by
    rw [hV]
    exact vertexLabels_injective a hnd
  have hm : ∀ i ∈ AppbPatternKind.s32three.pattern.vertices,f i ∈ M.atoms := by
    intro i hi
    rw [hV] at hi
    exact hmem _ (vertexLabels_mem a hi)
  apply realizationOfTable M AppbPatternKind.s32three.pattern f hf hm data.s32Enumeration
    (data.s32Enumeration_injective hab) data.s32Enumeration_outgoing ?_ (by decide) ?_
  · intro i
    have hh := data.s32_endpoints i
    fin_cases i <;> simpa [f,vertexLabels,AppbPatternKind.pattern,hl0,hl1,hr0] using hh
  · intro i hi
    have hi' : i = 1 ∨ i = 2 := by
      simpa only [AppbPatternKind.pattern,mem_insert,mem_singleton] using hi
    rcases hi' with rfl | rfl
    · exact hda
    · exact hdb

noncomputable def s32fourRealization (M : Molecule V D)
    {a b c d : V} (hab : a ≠ b)
    (hnd : ([a,b,c,d] : List V).Nodup) (hmem : ∀ v ∈ ([a,b,c,d] : List V),v ∈ M.atoms)
    (hda : M.deg a = 3) (hdb : M.deg b = 2) (data : MixedPairEdges M a b 1 2 1)
    (hl0 : data.left.neighbor 0 = c)
    (hl1 : data.left.neighbor 1 = d)
    (hr0 : data.right.neighbor 0 = d)
    : AppbRealization M AppbPatternKind.s32four.pattern := by
  classical
  let f := vertexLabels [a,b,c,d] a
  have hV : AppbPatternKind.s32four.pattern.vertices = Icc 1 4 := by decide
  have hf : Set.InjOn f (AppbPatternKind.s32four.pattern.vertices : Set ℕ) := by
    rw [hV]
    exact vertexLabels_injective a hnd
  have hm : ∀ i ∈ AppbPatternKind.s32four.pattern.vertices,f i ∈ M.atoms := by
    intro i hi
    rw [hV] at hi
    exact hmem _ (vertexLabels_mem a hi)
  apply realizationOfTable M AppbPatternKind.s32four.pattern f hf hm data.s32Enumeration
    (data.s32Enumeration_injective hab) data.s32Enumeration_outgoing ?_ (by decide) ?_
  · intro i
    have hh := data.s32_endpoints i
    fin_cases i <;> simpa [f,vertexLabels,AppbPatternKind.pattern,hl0,hl1,hr0] using hh
  · intro i hi
    have hi' : i = 1 ∨ i = 2 := by
      simpa only [AppbPatternKind.pattern,mem_insert,mem_singleton] using hi
    rcases hi' with rfl | rfl
    · exact hda
    · exact hdb

end WaveTurbulence.Mole.AppbAlgorithm
