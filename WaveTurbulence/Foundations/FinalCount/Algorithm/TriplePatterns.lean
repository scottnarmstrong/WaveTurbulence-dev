/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.MixedPairEdges
public import WaveTurbulence.Foundations.FinalCount.Algorithm.VertexLabels
public import WaveTurbulence.Foundations.FinalCount.Algorithm.TableRealization
import Mathlib.Tactic

/-! # Complete old-edge realizations of the two source triple-bond groups -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def tb1Realization (M : Molecule V D)
    {a b : V} (hab : a ≠ b) (hnd : ([a,b] : List V).Nodup)
    (hmem : ∀ v ∈ ([a,b] : List V),v ∈ M.atoms)
    (hda : M.deg a = 3) (hdb : M.deg b = 3) (data : MixedPairEdges M a b 3 0 0)
     :
    AppbRealization M AppbPatternKind.tb1.pattern := by
  classical
  let f := vertexLabels [a,b] a
  have hV : AppbPatternKind.tb1.pattern.vertices = Icc 1 2 := by decide
  have hf : Set.InjOn f (AppbPatternKind.tb1.pattern.vertices : Set ℕ) := by
    rw [hV]
    exact vertexLabels_injective a hnd
  have hm : ∀ i ∈ AppbPatternKind.tb1.pattern.vertices,f i ∈ M.atoms := by
    intro i hi
    rw [hV] at hi
    exact hmem _ (vertexLabels_mem a hi)
  apply realizationOfTable M AppbPatternKind.tb1.pattern f hf hm data.enumeration
    (data.enumeration_injective hab) data.enumeration_outgoing ?_ (by decide) ?_
  · intro i
    fin_cases i
    · exact (mem_filter.mp (data.middle 0).property).2
    · exact (mem_filter.mp (data.middle 1).property).2
    · exact (mem_filter.mp (data.middle 2).property).2
  · intro i hi
    have hi' : i = 1 ∨ i = 2 := by
      simpa only [AppbPatternKind.pattern,mem_insert,mem_singleton] using hi
    rcases hi' with rfl | rfl
    · exact hda
    · exact hdb

noncomputable def tb2Realization (M : Molecule V D)
    {a b c : V} (hab : a ≠ b) (hnd : ([a,b,c] : List V).Nodup)
    (hmem : ∀ v ∈ ([a,b,c] : List V),v ∈ M.atoms)
    (hda : M.deg a = 3) (hdb : M.deg b = 4) (data : MixedPairEdges M a b 3 0 1)
    (htail : data.right.neighbor 0 = c) :
    AppbRealization M AppbPatternKind.tb2.pattern := by
  classical
  let f := vertexLabels [a,b,c] a
  have hV : AppbPatternKind.tb2.pattern.vertices = Icc 1 3 := by decide
  have hf : Set.InjOn f (AppbPatternKind.tb2.pattern.vertices : Set ℕ) := by
    rw [hV]
    exact vertexLabels_injective a hnd
  have hm : ∀ i ∈ AppbPatternKind.tb2.pattern.vertices,f i ∈ M.atoms := by
    intro i hi
    rw [hV] at hi
    exact hmem _ (vertexLabels_mem a hi)
  apply realizationOfTable M AppbPatternKind.tb2.pattern f hf hm data.enumeration
    (data.enumeration_injective hab) data.enumeration_outgoing ?_ (by decide) ?_
  · intro i
    fin_cases i
    · exact (mem_filter.mp (data.middle 0).property).2
    · exact (mem_filter.mp (data.middle 1).property).2
    · exact (mem_filter.mp (data.middle 2).property).2
    · change M.ends (data.right.edge (0 : Fin 1)).val = s(b,c)
      simpa only [htail] using data.right.endpoints 0
  · intro i hi
    have hi' : i = 1 ∨ i = 2 := by
      simpa only [AppbPatternKind.pattern,mem_insert,mem_singleton] using hi
    rcases hi' with rfl | rfl
    · exact hda
    · exact hdb

end WaveTurbulence.Mole.AppbAlgorithm
