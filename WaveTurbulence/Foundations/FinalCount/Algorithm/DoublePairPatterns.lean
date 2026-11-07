/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.DoublePairEdges
public import WaveTurbulence.Foundations.FinalCount.Algorithm.TableRealization
import Mathlib.Tactic

/-! # Actual double-bond pair figures from their old degree-three centers -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def distinctDoublePairRealization (M : Molecule V D)
    {a b c d : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms)
    (hc : c ∈ M.atoms) (hd : d ∈ M.atoms)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hda : d ≠ a) (hdb : d ≠ b) (hcd : c ≠ d)
    (hdegA : M.deg a = 3) (hdegB : M.deg b = 3)
    (edges : DoublePairEdges M a b c d) :
    AppbRealization M AppbPatternKind.d33.pattern := by
  classical
  let f := fun i : ℕ => if i = 1 then a else if i = 2 then b else if i = 3 then c else d
  have hV : AppbPatternKind.d33.pattern.vertices = {1,2,3,4} := by decide
  apply realizationOfTable M AppbPatternKind.d33.pattern f ?_ ?_ edges.edge edges.injective edges.outgoing ?_ ?_ ?_
  · intro i hi j hj hij
    have hi' : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
      simpa only [Finset.mem_coe,hV,mem_insert,mem_singleton] using hi
    have hj' : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by
      simpa only [Finset.mem_coe,hV,mem_insert,mem_singleton] using hj
    rcases hi' with rfl | rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl | rfl
    all_goals simp only [f,ite_true,Nat.reduceEqDiff,ite_false] at hij
    all_goals first
      | rfl
      | exact (hab hij).elim
      | exact (hab hij.symm).elim
      | exact (hca hij).elim
      | exact (hca hij.symm).elim
      | exact (hcb hij).elim
      | exact (hcb hij.symm).elim
      | exact (hda hij).elim
      | exact (hda hij.symm).elim
      | exact (hdb hij).elim
      | exact (hdb hij.symm).elim
      | exact (hcd hij).elim
      | exact (hcd hij.symm).elim
  · intro i hi
    have hi' : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
      simpa only [hV,mem_insert,mem_singleton] using hi
    rcases hi' with rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  · intro i
    have he := edges.endpoints i
    fin_cases i <;> exact he
  · decide
  · intro i hi
    have hi' : i = 1 ∨ i = 2 := by
      simpa only [AppbPatternKind.pattern,mem_insert,mem_singleton] using hi
    rcases hi' with rfl | rfl
    · exact hdegA
    · exact hdegB

noncomputable def commonDoublePairRealization (M : Molecule V D)
    {a b c : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms)
    (hc : c ∈ M.atoms)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    
    (hdegA : M.deg a = 3) (hdegB : M.deg b = 3)
    (edges : DoublePairEdges M a b c c) :
    AppbRealization M AppbPatternKind.d33same.pattern := by
  classical
  let f := fun i : ℕ => if i = 1 then a else if i = 2 then b else c
  have hV : AppbPatternKind.d33same.pattern.vertices = {1,2,3} := by decide
  apply realizationOfTable M AppbPatternKind.d33same.pattern f ?_ ?_ edges.edge edges.injective edges.outgoing ?_ ?_ ?_
  · intro i hi j hj hij
    have hi' : i = 1 ∨ i = 2 ∨ i = 3 := by
      simpa only [Finset.mem_coe,hV,mem_insert,mem_singleton] using hi
    have hj' : j = 1 ∨ j = 2 ∨ j = 3 := by
      simpa only [Finset.mem_coe,hV,mem_insert,mem_singleton] using hj
    rcases hi' with rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl
    all_goals simp only [f,ite_true,Nat.reduceEqDiff,ite_false] at hij
    all_goals first
      | rfl
      | exact (hab hij).elim
      | exact (hab hij.symm).elim
      | exact (hca hij).elim
      | exact (hca hij.symm).elim
      | exact (hcb hij).elim
      | exact (hcb hij.symm).elim
  · intro i hi
    have hi' : i = 1 ∨ i = 2 ∨ i = 3 := by
      simpa only [hV,mem_insert,mem_singleton] using hi
    rcases hi' with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  · intro i
    have he := edges.endpoints i
    fin_cases i <;> exact he
  · decide
  · intro i hi
    have hi' : i = 1 ∨ i = 2 := by
      simpa only [AppbPatternKind.pattern,mem_insert,mem_singleton] using hi
    rcases hi' with rfl | rfl
    · exact hdegA
    · exact hdegB

end WaveTurbulence.Mole.AppbAlgorithm
