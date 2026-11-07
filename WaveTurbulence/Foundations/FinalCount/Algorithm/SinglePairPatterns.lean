/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SinglePairEnumeration
public import WaveTurbulence.Foundations.FinalCount.Algorithm.VertexLabels
public import WaveTurbulence.Foundations.FinalCount.Algorithm.TableRealization
import Mathlib.Tactic

/-! # The seven literal single-pair profiles with complete old edge lists -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def s33Realization (M : Molecule V D)
    {a b c d p q : V} (hab : a ≠ b)
    (hnd : ([a,b,c,d,p,q] : List V).Nodup) (hmem : ∀ v ∈ ([a,b,c,d,p,q] : List V),v ∈ M.atoms)
    (hda : M.deg a = 3) (hdb : M.deg b = 3) (data : SinglePairEdges M a b)
    (hl0 : data.left.neighbor 0 = c) (hl1 : data.left.neighbor 1 = d)
    (hr0 : data.right.neighbor 0 = p) (hr1 : data.right.neighbor 1 = q) :
    AppbRealization M AppbPatternKind.s33.pattern := by
  classical
  let f := vertexLabels [a,b,c,d,p,q] a
  have hV : AppbPatternKind.s33.pattern.vertices = Icc 1 6 := by decide
  have hf : Set.InjOn f (AppbPatternKind.s33.pattern.vertices : Set ℕ) := by
    rw [hV]
    exact vertexLabels_injective a hnd
  have hm : ∀ i ∈ AppbPatternKind.s33.pattern.vertices,f i ∈ M.atoms := by
    intro i hi
    rw [hV] at hi
    exact hmem _ (vertexLabels_mem a hi)
  apply realizationOfTable M AppbPatternKind.s33.pattern f hf hm data.enumeration
    (data.enumeration_injective hab) data.enumeration_outgoing ?_ (by decide) ?_
  · intro i
    have hh := data.enumeration_endpoints i
    fin_cases i <;> simpa [f,vertexLabels,AppbPatternKind.pattern,hl0,hl1,hr0,hr1] using hh
  · intro i hi
    have hi' : i = 1 ∨ i = 2 := by
      simpa only [AppbPatternKind.pattern,mem_insert,mem_singleton] using hi
    rcases hi' with rfl | rfl
    · exact hda
    · exact hdb

noncomputable def s33new1Realization (M : Molecule V D)
    {a b c d p : V} (hab : a ≠ b)
    (hnd : ([a,b,c,d,p] : List V).Nodup) (hmem : ∀ v ∈ ([a,b,c,d,p] : List V),v ∈ M.atoms)
    (hda : M.deg a = 3) (hdb : M.deg b = 3) (data : SinglePairEdges M a b)
    (hl0 : data.left.neighbor 0 = c) (hl1 : data.left.neighbor 1 = d)
    (hr0 : data.right.neighbor 0 = c) (hr1 : data.right.neighbor 1 = p) :
    AppbRealization M AppbPatternKind.s33new1.pattern := by
  classical
  let f := vertexLabels [a,b,c,d,p] a
  have hV : AppbPatternKind.s33new1.pattern.vertices = Icc 1 5 := by decide
  have hf : Set.InjOn f (AppbPatternKind.s33new1.pattern.vertices : Set ℕ) := by
    rw [hV]
    exact vertexLabels_injective a hnd
  have hm : ∀ i ∈ AppbPatternKind.s33new1.pattern.vertices,f i ∈ M.atoms := by
    intro i hi
    rw [hV] at hi
    exact hmem _ (vertexLabels_mem a hi)
  apply realizationOfTable M AppbPatternKind.s33new1.pattern f hf hm data.enumeration
    (data.enumeration_injective hab) data.enumeration_outgoing ?_ (by decide) ?_
  · intro i
    have hh := data.enumeration_endpoints i
    fin_cases i <;> simpa [f,vertexLabels,AppbPatternKind.pattern,hl0,hl1,hr0,hr1] using hh
  · intro i hi
    have hi' : i = 1 ∨ i = 2 := by
      simpa only [AppbPatternKind.pattern,mem_insert,mem_singleton] using hi
    rcases hi' with rfl | rfl
    · exact hda
    · exact hdb

noncomputable def s33new2Realization (M : Molecule V D)
    {a b c d : V} (hab : a ≠ b)
    (hnd : ([a,b,c,d] : List V).Nodup) (hmem : ∀ v ∈ ([a,b,c,d] : List V),v ∈ M.atoms)
    (hda : M.deg a = 3) (hdb : M.deg b = 3) (data : SinglePairEdges M a b)
    (hl0 : data.left.neighbor 0 = c) (hl1 : data.left.neighbor 1 = d)
    (hr0 : data.right.neighbor 0 = c) (hr1 : data.right.neighbor 1 = d) :
    AppbRealization M AppbPatternKind.s33new2.pattern := by
  classical
  let f := vertexLabels [a,b,c,d] a
  have hV : AppbPatternKind.s33new2.pattern.vertices = Icc 1 4 := by decide
  have hf : Set.InjOn f (AppbPatternKind.s33new2.pattern.vertices : Set ℕ) := by
    rw [hV]
    exact vertexLabels_injective a hnd
  have hm : ∀ i ∈ AppbPatternKind.s33new2.pattern.vertices,f i ∈ M.atoms := by
    intro i hi
    rw [hV] at hi
    exact hmem _ (vertexLabels_mem a hi)
  apply realizationOfTable M AppbPatternKind.s33new2.pattern f hf hm data.enumeration
    (data.enumeration_injective hab) data.enumeration_outgoing ?_ (by decide) ?_
  · intro i
    have hh := data.enumeration_endpoints i
    fin_cases i <;> simpa [f,vertexLabels,AppbPatternKind.pattern,hl0,hl1,hr0,hr1] using hh
  · intro i hi
    have hi' : i = 1 ∨ i = 2 := by
      simpa only [AppbPatternKind.pattern,mem_insert,mem_singleton] using hi
    rcases hi' with rfl | rfl
    · exact hda
    · exact hdb

noncomputable def s33new3Realization (M : Molecule V D)
    {a b c d : V} (hab : a ≠ b)
    (hnd : ([a,b,c,d] : List V).Nodup) (hmem : ∀ v ∈ ([a,b,c,d] : List V),v ∈ M.atoms)
    (hda : M.deg a = 3) (hdb : M.deg b = 3) (data : SinglePairEdges M a b)
    (hl0 : data.left.neighbor 0 = c) (hl1 : data.left.neighbor 1 = c)
    (hr0 : data.right.neighbor 0 = d) (hr1 : data.right.neighbor 1 = d) :
    AppbRealization M AppbPatternKind.s33new3.pattern := by
  classical
  let f := vertexLabels [a,b,c,d] a
  have hV : AppbPatternKind.s33new3.pattern.vertices = Icc 1 4 := by decide
  have hf : Set.InjOn f (AppbPatternKind.s33new3.pattern.vertices : Set ℕ) := by
    rw [hV]
    exact vertexLabels_injective a hnd
  have hm : ∀ i ∈ AppbPatternKind.s33new3.pattern.vertices,f i ∈ M.atoms := by
    intro i hi
    rw [hV] at hi
    exact hmem _ (vertexLabels_mem a hi)
  apply realizationOfTable M AppbPatternKind.s33new3.pattern f hf hm data.enumeration
    (data.enumeration_injective hab) data.enumeration_outgoing ?_ (by decide) ?_
  · intro i
    have hh := data.enumeration_endpoints i
    fin_cases i <;> simpa [f,vertexLabels,AppbPatternKind.pattern,hl0,hl1,hr0,hr1] using hh
  · intro i hi
    have hi' : i = 1 ∨ i = 2 := by
      simpa only [AppbPatternKind.pattern,mem_insert,mem_singleton] using hi
    rcases hi' with rfl | rfl
    · exact hda
    · exact hdb

noncomputable def s33new4Realization (M : Molecule V D)
    {a b c : V} (hab : a ≠ b)
    (hnd : ([a,b,c] : List V).Nodup) (hmem : ∀ v ∈ ([a,b,c] : List V),v ∈ M.atoms)
    (hda : M.deg a = 3) (hdb : M.deg b = 3) (data : SinglePairEdges M a b)
    (hl0 : data.left.neighbor 0 = c) (hl1 : data.left.neighbor 1 = c)
    (hr0 : data.right.neighbor 0 = c) (hr1 : data.right.neighbor 1 = c) :
    AppbRealization M AppbPatternKind.s33new4.pattern := by
  classical
  let f := vertexLabels [a,b,c] a
  have hV : AppbPatternKind.s33new4.pattern.vertices = Icc 1 3 := by decide
  have hf : Set.InjOn f (AppbPatternKind.s33new4.pattern.vertices : Set ℕ) := by
    rw [hV]
    exact vertexLabels_injective a hnd
  have hm : ∀ i ∈ AppbPatternKind.s33new4.pattern.vertices,f i ∈ M.atoms := by
    intro i hi
    rw [hV] at hi
    exact hmem _ (vertexLabels_mem a hi)
  apply realizationOfTable M AppbPatternKind.s33new4.pattern f hf hm data.enumeration
    (data.enumeration_injective hab) data.enumeration_outgoing ?_ (by decide) ?_
  · intro i
    have hh := data.enumeration_endpoints i
    fin_cases i <;> simpa [f,vertexLabels,AppbPatternKind.pattern,hl0,hl1,hr0,hr1] using hh
  · intro i hi
    have hi' : i = 1 ∨ i = 2 := by
      simpa only [AppbPatternKind.pattern,mem_insert,mem_singleton] using hi
    rcases hi' with rfl | rfl
    · exact hda
    · exact hdb

noncomputable def s33new5Realization (M : Molecule V D)
    {a b c d p : V} (hab : a ≠ b)
    (hnd : ([a,b,c,d,p] : List V).Nodup) (hmem : ∀ v ∈ ([a,b,c,d,p] : List V),v ∈ M.atoms)
    (hda : M.deg a = 3) (hdb : M.deg b = 3) (data : SinglePairEdges M a b)
    (hl0 : data.left.neighbor 0 = c) (hl1 : data.left.neighbor 1 = c)
    (hr0 : data.right.neighbor 0 = d) (hr1 : data.right.neighbor 1 = p) :
    AppbRealization M AppbPatternKind.s33new5.pattern := by
  classical
  let f := vertexLabels [a,b,c,d,p] a
  have hV : AppbPatternKind.s33new5.pattern.vertices = Icc 1 5 := by decide
  have hf : Set.InjOn f (AppbPatternKind.s33new5.pattern.vertices : Set ℕ) := by
    rw [hV]
    exact vertexLabels_injective a hnd
  have hm : ∀ i ∈ AppbPatternKind.s33new5.pattern.vertices,f i ∈ M.atoms := by
    intro i hi
    rw [hV] at hi
    exact hmem _ (vertexLabels_mem a hi)
  apply realizationOfTable M AppbPatternKind.s33new5.pattern f hf hm data.enumeration
    (data.enumeration_injective hab) data.enumeration_outgoing ?_ (by decide) ?_
  · intro i
    have hh := data.enumeration_endpoints i
    fin_cases i <;> simpa [f,vertexLabels,AppbPatternKind.pattern,hl0,hl1,hr0,hr1] using hh
  · intro i hi
    have hi' : i = 1 ∨ i = 2 := by
      simpa only [AppbPatternKind.pattern,mem_insert,mem_singleton] using hi
    rcases hi' with rfl | rfl
    · exact hda
    · exact hdb

noncomputable def s33new6Realization (M : Molecule V D)
    {a b c d : V} (hab : a ≠ b)
    (hnd : ([a,b,c,d] : List V).Nodup) (hmem : ∀ v ∈ ([a,b,c,d] : List V),v ∈ M.atoms)
    (hda : M.deg a = 3) (hdb : M.deg b = 3) (data : SinglePairEdges M a b)
    (hl0 : data.left.neighbor 0 = c) (hl1 : data.left.neighbor 1 = c)
    (hr0 : data.right.neighbor 0 = c) (hr1 : data.right.neighbor 1 = d) :
    AppbRealization M AppbPatternKind.s33new6.pattern := by
  classical
  let f := vertexLabels [a,b,c,d] a
  have hV : AppbPatternKind.s33new6.pattern.vertices = Icc 1 4 := by decide
  have hf : Set.InjOn f (AppbPatternKind.s33new6.pattern.vertices : Set ℕ) := by
    rw [hV]
    exact vertexLabels_injective a hnd
  have hm : ∀ i ∈ AppbPatternKind.s33new6.pattern.vertices,f i ∈ M.atoms := by
    intro i hi
    rw [hV] at hi
    exact hmem _ (vertexLabels_mem a hi)
  apply realizationOfTable M AppbPatternKind.s33new6.pattern f hf hm data.enumeration
    (data.enumeration_injective hab) data.enumeration_outgoing ?_ (by decide) ?_
  · intro i
    have hh := data.enumeration_endpoints i
    fin_cases i <;> simpa [f,vertexLabels,AppbPatternKind.pattern,hl0,hl1,hr0,hr1] using hh
  · intro i hi
    have hi' : i = 1 ∨ i = 2 := by
      simpa only [AppbPatternKind.pattern,mem_insert,mem_singleton] using hi
    rcases hi' with rfl | rfl
    · exact hda
    · exact hdb

end WaveTurbulence.Mole.AppbAlgorithm
