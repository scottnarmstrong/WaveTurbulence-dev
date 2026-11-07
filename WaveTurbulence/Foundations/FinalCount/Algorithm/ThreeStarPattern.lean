/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.StarMultiplicity
import Mathlib.Tactic

/-! # The actual three-distinct-neighbor star in rule six -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace Star
variable {M : Molecule V D} {v : V} (st : Star M v 3)

noncomputable def threeRealization (hv : v ∈ M.atoms)
    (hinj : Function.Injective st.neighbor) :
    AppbRealization M AppbPatternKind.r3.pattern := by
  classical
  have hV : AppbPatternKind.r3.pattern.vertices = {1,2,3,4} := by decide
  let f := fun a : ℕ => if a = 1 then v else if a = 2 then st.neighbor 0
    else if a = 3 then st.neighbor 1 else st.neighbor 2
  have hY : AppbPatternKind.r3.pattern.removed.image f = {v} := by
    change ({1} : Finset ℕ).image f = {v}
    simp only [image_singleton]
    rfl
  have h01 : st.neighbor 0 ≠ st.neighbor 1 := fun h => by simpa using hinj h
  have h02 : st.neighbor 0 ≠ st.neighbor 2 := fun h => by simpa using hinj h
  have h12 : st.neighbor 1 ≠ st.neighbor 2 := fun h => by simpa using hinj h
  exact {
    vertex := f
    vertex_injective := by
      intro a ha b hb hab
      have ha' : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by
        simpa only [Finset.mem_coe,hV,mem_insert,mem_singleton] using ha
      have hb' : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by
        simpa only [Finset.mem_coe,hV,mem_insert,mem_singleton] using hb
      rcases ha' with rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl
      all_goals simp only [f,ite_true,Nat.reduceEqDiff,ite_false] at hab
      all_goals first
        | rfl
        | exact (st.neighbor_ne 0 hab).elim
        | exact (st.neighbor_ne 0 hab.symm).elim
        | exact (st.neighbor_ne 1 hab).elim
        | exact (st.neighbor_ne 1 hab.symm).elim
        | exact (st.neighbor_ne 2 hab).elim
        | exact (st.neighbor_ne 2 hab.symm).elim
        | exact (h01 hab).elim
        | exact (h01 hab.symm).elim
        | exact (h02 hab).elim
        | exact (h02 hab.symm).elim
        | exact (h12 hab).elim
        | exact (h12 hab.symm).elim
    vertex_mem := by
      intro a ha
      have ha' : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by
        simpa only [hV,mem_insert,mem_singleton] using ha
      rcases ha' with rfl | rfl | rfl | rfl
      · exact hv
      · exact st.neighbor_mem 0
      · exact st.neighbor_mem 1
      · exact st.neighbor_mem 2
    edge := st.edge.trans (Equiv.subtypeEquivRight (fun x => by rw [hY]))
    endpoints := by
      intro i
      have hh := st.endpoints i
      fin_cases i <;> exact hh
  }

end Star
end WaveTurbulence.Mole.AppbAlgorithm
