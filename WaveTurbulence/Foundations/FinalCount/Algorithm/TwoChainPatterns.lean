/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SimpleTableEdges
public import WaveTurbulence.Foundations.FinalCount.Algorithm.VertexLabels
import Mathlib.Tactic

/-! # Literal degree-two chain and triangle realizations for rule seven -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def triangleTwoChain (M : Molecule V D)
    {a b c : V} (hnd : ([a,b,c] : List V).Nodup)
    (hmem : ∀ v ∈ ([a,b,c] : List V),v ∈ M.atoms)
    (hda : M.deg a = 2) (hdb : M.deg b = 2) (hdc : M.deg c = 2)
    (edge : Fin 3 → D) (hout : ∀ i,M.out (edge i) = true)
    (hend : ∀ i,M.ends (edge i) = (![s(a,b),s(a,c),s(b,c)] : Fin 3 → Sym2 V) i) :
    AppbRealization M AppbPatternKind.r23triangle.pattern := by
  classical
  let f := vertexLabels [a,b,c] a
  have hV : (AppbPatternKind.r23triangle.pattern).vertices = Icc 1 3 := by decide
  have hf : Set.InjOn f ((AppbPatternKind.r23triangle.pattern).vertices : Set ℕ) := by
    rw [hV]
    exact vertexLabels_injective a hnd
  have hm : ∀ i ∈ (AppbPatternKind.r23triangle.pattern).vertices,f i ∈ M.atoms := by
    intro i hi
    rw [hV] at hi
    exact hmem _ (vertexLabels_mem a hi)
  have he : ∀ i : Fin 3,M.ends (edge i) = s(f (AppbPatternKind.r23triangle.pattern).edges[i].1,f (AppbPatternKind.r23triangle.pattern).edges[i].2) := by
    intro i
    have hh := hend i
    fin_cases i <;> simpa [f,vertexLabels,AppbPatternKind.pattern,appbR23Common] using hh
  apply realizationOfTable M AppbPatternKind.r23triangle.pattern f hf hm edge
    (table_edges_injective_of_simple M AppbPatternKind.r23triangle.pattern f hf (by decide) edge he) hout he (by decide)
  intro i hi
  have hi' : i = 1 ∨ i = 2 ∨ i = 3 := by
    simpa only [AppbPatternKind.pattern,mem_insert,mem_singleton] using hi
  rcases hi' with rfl | rfl | rfl
  · exact hda
  · exact hdb
  · exact hdc

noncomputable def commonTwoChain (M : Molecule V D)
    {a b c d : V} (hnd : ([a,b,c,d] : List V).Nodup)
    (hmem : ∀ v ∈ ([a,b,c,d] : List V),v ∈ M.atoms)
    (hda : M.deg a = 2) (hdb : M.deg b = 2) (hdc : M.deg c = 2)
    (edge : Fin 4 → D) (hout : ∀ i,M.out (edge i) = true)
    (hend : ∀ i,M.ends (edge i) = (![s(a,b),s(a,c),s(b,d),s(c,d)] : Fin 4 → Sym2 V) i) :
    AppbRealization M appbR23Common := by
  classical
  let f := vertexLabels [a,b,c,d] a
  have hV : (appbR23Common).vertices = Icc 1 4 := by decide
  have hf : Set.InjOn f ((appbR23Common).vertices : Set ℕ) := by
    rw [hV]
    exact vertexLabels_injective a hnd
  have hm : ∀ i ∈ (appbR23Common).vertices,f i ∈ M.atoms := by
    intro i hi
    rw [hV] at hi
    exact hmem _ (vertexLabels_mem a hi)
  have he : ∀ i : Fin 4,M.ends (edge i) = s(f (appbR23Common).edges[i].1,f (appbR23Common).edges[i].2) := by
    intro i
    have hh := hend i
    fin_cases i <;> simpa [f,vertexLabels,AppbPatternKind.pattern,appbR23Common] using hh
  apply realizationOfTable M appbR23Common f hf hm edge
    (table_edges_injective_of_simple M appbR23Common f hf (by decide) edge he) hout he (by decide)
  intro i hi
  have hi' : i = 1 ∨ i = 2 ∨ i = 3 := by
    simpa only [appbR23Common,mem_insert,mem_singleton] using hi
  rcases hi' with rfl | rfl | rfl
  · exact hda
  · exact hdb
  · exact hdc

noncomputable def openTwoChain (M : Molecule V D)
    {a b c d e : V} (hnd : ([a,b,c,d,e] : List V).Nodup)
    (hmem : ∀ v ∈ ([a,b,c,d,e] : List V),v ∈ M.atoms)
    (hda : M.deg a = 2) (hdb : M.deg b = 2) (hdc : M.deg c = 2)
    (edge : Fin 4 → D) (hout : ∀ i,M.out (edge i) = true)
    (hend : ∀ i,M.ends (edge i) = (![s(a,b),s(a,c),s(b,d),s(c,e)] : Fin 4 → Sym2 V) i) :
    AppbRealization M AppbPatternKind.r23.pattern := by
  classical
  let f := vertexLabels [a,b,c,d,e] a
  have hV : (AppbPatternKind.r23.pattern).vertices = Icc 1 5 := by decide
  have hf : Set.InjOn f ((AppbPatternKind.r23.pattern).vertices : Set ℕ) := by
    rw [hV]
    exact vertexLabels_injective a hnd
  have hm : ∀ i ∈ (AppbPatternKind.r23.pattern).vertices,f i ∈ M.atoms := by
    intro i hi
    rw [hV] at hi
    exact hmem _ (vertexLabels_mem a hi)
  have he : ∀ i : Fin 4,M.ends (edge i) = s(f (AppbPatternKind.r23.pattern).edges[i].1,f (AppbPatternKind.r23.pattern).edges[i].2) := by
    intro i
    have hh := hend i
    fin_cases i <;> simpa [f,vertexLabels,AppbPatternKind.pattern,appbR23Common] using hh
  apply realizationOfTable M AppbPatternKind.r23.pattern f hf hm edge
    (table_edges_injective_of_simple M AppbPatternKind.r23.pattern f hf (by decide) edge he) hout he (by decide)
  intro i hi
  have hi' : i = 1 ∨ i = 2 ∨ i = 3 := by
    simpa only [AppbPatternKind.pattern,mem_insert,mem_singleton] using hi
  rcases hi' with rfl | rfl | rfl
  · exact hda
  · exact hdb
  · exact hdc

end WaveTurbulence.Mole.AppbAlgorithm
