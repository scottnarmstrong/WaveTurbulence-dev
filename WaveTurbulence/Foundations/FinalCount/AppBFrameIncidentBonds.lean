/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBTripleFrame
import Mathlib.Tactic

/-! # An actual degree-three frame enumerates every incident physical bond -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_incidence_zero_iff (M : Molecule V D) (a : V) (x : D) :
    appbIncidence M a x = 0 ↔ M.atom x ≠ a ∧ M.atom (M.mate x) ≠ a := by
  by_cases ha : M.atom x = a <;> by_cases hb : M.atom (M.mate x) = a
  all_goals simp [appbIncidence,ha,hb]

namespace AppbTripleFrame
variable {M : Molecule V D} {P : AppbPattern} {r : AppbRealization M P} {v : V}
    (t : AppbTripleFrame r v)

theorem incident_bonds (hv : v ∈ r.removedAtoms) :
    appbRemovedBonds M {v} =
      {(r.edge (t.index 0)).val,(r.edge (t.index 1)).val,(r.edge (t.index 2)).val} := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨hb,ht⟩ := mem_filter.mp hx
    have ht' : M.atom x = v ∨ M.atom (M.mate x) = v := by simpa only [mem_singleton] using ht
    have hlocal : x ∈ appbRemovedBonds M r.removedAtoms := mem_filter.mpr ⟨hb,ht'.imp (fun (h : M.atom x = v) => h.symm ▸ hv) (fun (h : M.atom (M.mate x) = v) => h.symm ▸ hv)⟩
    obtain ⟨i,hi⟩ := r.edge.surjective ⟨x,hlocal⟩
    have hval : (r.edge i).val = x := congrArg Subtype.val hi
    have hnonzero : appbIncidence M v (r.edge i).val ≠ 0 := by
      intro hz
      rw [hval] at hz
      have hh := (appb_incidence_zero_iff M v x).mp hz
      tauto
    have hex : ∃ j,t.index j = i := by
      by_contra hn
      apply hnonzero
      apply t.other
      intro j hj
      exact hn ⟨j,hj⟩
    obtain ⟨j,rfl⟩ := hex
    rw [← hval]
    simp only [mem_insert,mem_singleton]
    fin_cases j
    · apply Or.inl
      exact congrArg (fun k : Fin 3 => (r.edge (t.index k)).val) (by decide : (⟨0,by decide⟩ : Fin 3) = 0)
    · apply Or.inr ∘ Or.inl
      exact congrArg (fun k : Fin 3 => (r.edge (t.index k)).val) (by decide : (⟨1,by decide⟩ : Fin 3) = 1)
    · apply Or.inr ∘ Or.inr
      exact congrArg (fun k : Fin 3 => (r.edge (t.index k)).val) (by decide : (⟨2,by decide⟩ : Fin 3) = 2)
  · intro hx
    have hcases : x = (r.edge (t.index 0)).val ∨ x = (r.edge (t.index 1)).val ∨ x = (r.edge (t.index 2)).val := by
      simpa only [mem_insert,mem_singleton] using hx
    have hmem (j : Fin 3) : (r.edge (t.index j)).val ∈ appbRemovedBonds M {v} := by
      apply mem_filter.mpr
      refine ⟨(mem_filter.mp (r.edge (t.index j)).property).1,?_⟩
      simp only [mem_singleton]
      by_contra hn
      have hz : appbIncidence M v (r.edge (t.index j)).val = 0 :=
        (appb_incidence_zero_iff M v _).mpr (by tauto)
      have ho := t.incidence j
      omega
    rcases hcases with rfl | rfl | rfl
    · exact hmem 0
    · exact hmem 1
    · exact hmem 2

end AppbTripleFrame
end WaveTurbulence.Mole
