/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.Star
import Mathlib.Tactic

/-! # The actual two-bond star is a double bond or two distinct single bonds -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace Star
variable {M : Molecule V D} {v : V} (st : Star M v 2)

noncomputable def doubleRealization (hv : v ∈ M.atoms) (heq : st.neighbor 0 = st.neighbor 1) :
    AppbRealization M AppbPatternKind.r21.pattern := by
  classical
  have hV : AppbPatternKind.r21.pattern.vertices = {1,2} := by decide
  let f := fun a : ℕ => if a = 1 then v else st.neighbor 0
  have hY : AppbPatternKind.r21.pattern.removed.image f = {v} := by
    change ({1} : Finset ℕ).image f = {v}
    simp only [image_singleton]
    rfl
  exact {
    vertex := f
    vertex_injective := by
      intro a ha b hb hab
      have ha' : a = 1 ∨ a = 2 := by simpa only [Finset.mem_coe,hV,mem_insert,mem_singleton] using ha
      have hb' : b = 1 ∨ b = 2 := by simpa only [Finset.mem_coe,hV,mem_insert,mem_singleton] using hb
      rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
      all_goals simp only [f,ite_true,Nat.reduceEqDiff,ite_false] at hab
      all_goals first | rfl | exact (st.neighbor_ne 0 hab).elim | exact (st.neighbor_ne 0 hab.symm).elim
    vertex_mem := by
      intro a ha
      have ha' : a = 1 ∨ a = 2 := by simpa only [Finset.mem_coe,hV,mem_insert,mem_singleton] using ha
      rcases ha' with rfl | rfl
      · exact hv
      · exact st.neighbor_mem 0
    edge := st.edge.trans (Equiv.subtypeEquivRight (fun x => by rw [hY]))
    endpoints := by
      intro i
      fin_cases i
      · change M.ends (st.edge (0 : Fin 2)).val = s(v,st.neighbor 0)
        exact st.endpoints 0
      · change M.ends (st.edge (1 : Fin 2)).val = s(v,st.neighbor 0)
        simpa only [heq] using st.endpoints 1
  }

noncomputable def singleRealization (hv : v ∈ M.atoms) (hne : st.neighbor 0 ≠ st.neighbor 1) :
    AppbRealization M AppbPatternKind.r22.pattern := by
  classical
  have hV : AppbPatternKind.r22.pattern.vertices = {1,2,3} := by decide
  let f := fun a : ℕ => if a = 1 then v else if a = 2 then st.neighbor 0 else st.neighbor 1
  have hY : AppbPatternKind.r22.pattern.removed.image f = {v} := by
    change ({1} : Finset ℕ).image f = {v}
    simp only [image_singleton]
    rfl
  exact {
    vertex := f
    vertex_injective := by
      intro a ha b hb hab
      have ha' : a = 1 ∨ a = 2 ∨ a = 3 := by simpa only [Finset.mem_coe,hV,mem_insert,mem_singleton] using ha
      have hb' : b = 1 ∨ b = 2 ∨ b = 3 := by simpa only [Finset.mem_coe,hV,mem_insert,mem_singleton] using hb
      rcases ha' with rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl
      all_goals simp only [f,ite_true,Nat.reduceEqDiff,ite_false] at hab
      all_goals first
        | rfl
        | exact (st.neighbor_ne 0 hab).elim
        | exact (st.neighbor_ne 0 hab.symm).elim
        | exact (st.neighbor_ne 1 hab).elim
        | exact (st.neighbor_ne 1 hab.symm).elim
        | exact (hne hab).elim
        | exact (hne hab.symm).elim
    vertex_mem := by
      intro a ha
      have ha' : a = 1 ∨ a = 2 ∨ a = 3 := by simpa only [Finset.mem_coe,hV,mem_insert,mem_singleton] using ha
      rcases ha' with rfl | rfl | rfl
      · exact hv
      · exact st.neighbor_mem 0
      · exact st.neighbor_mem 1
    edge := st.edge.trans (Equiv.subtypeEquivRight (fun x => by rw [hY]))
    endpoints := by
      intro i
      have hh := st.endpoints i
      fin_cases i
      · exact hh
      · exact hh
  }

end Star
end WaveTurbulence.Mole.AppbAlgorithm
