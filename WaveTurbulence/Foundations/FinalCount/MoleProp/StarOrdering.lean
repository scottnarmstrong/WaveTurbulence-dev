/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.StarEquations
import Mathlib.Tactic

/-! # Alternating enumeration of the actual degree-three atom incidences -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- DH23 basiccount(2) applies to every degree-three molecule atom:
the actual two-in/two-out cap supplies an alternating enumeration. -/
theorem exists_alternating_star_order (M : Molecule V D) (hM : M.IsMolecule)
    {v : V} (hv : v ∈ M.atoms) (hd : M.deg v = 3) :
    ∃ (e : Fin 3 ≃ IncidentDart M v) (b : Bool),
      M.out (e 0).val = b ∧ M.out (e 1).val = !b ∧ M.out (e 2).val = b := by
  classical
  let e : Fin 3 ≃ IncidentDart M v := (Fintype.equivFinOfCardEq ((card_incidentDart M v).trans hd)).symm
  have hnot (b : Bool) : ¬ (∀ i : Fin 3, M.out (e i).val = b) := by
    intro hall
    have hall' (x : D) (hx : x ∈ M.dartsAt v) : M.out x = b := by
      obtain ⟨i,hi⟩ := e.surjective ⟨x,(Mole.mem_dartsAt M v x).mp hx⟩
      have hh := hall i
      simpa only [hi] using hh
    cases b
    · have he : (M.dartsAt v).filter (fun x => M.out x = false) = M.dartsAt v :=
        filter_eq_self.mpr hall'
      have hcap := (hM.1 v hv).2
      change ((M.dartsAt v).filter (fun x => M.out x = false)).card ≤ 2 at hcap
      rw [he] at hcap
      change M.deg v ≤ 2 at hcap
      omega
    · have he : (M.dartsAt v).filter (fun x => M.out x = true) = M.dartsAt v :=
        filter_eq_self.mpr hall'
      have hcap := (hM.1 v hv).1
      change ((M.dartsAt v).filter (fun x => M.out x = true)).card ≤ 2 at hcap
      rw [he] at hcap
      change M.deg v ≤ 2 at hcap
      omega
  let e1 := (Equiv.swap (1 : Fin 3) 2).trans e
  let e2 := (Equiv.swap (0 : Fin 3) 1).trans e
  cases h0 : M.out (e 0).val <;> cases h1 : M.out (e 1).val <;> cases h2 : M.out (e 2).val
  · exact False.elim (hnot false (by intro i; fin_cases i <;> assumption))
  · refine ⟨e1,false,?_,?_,?_⟩ <;> simp [e1,Equiv.swap_apply_def,h0,h1,h2]
  · exact ⟨e,false,h0,h1,h2⟩
  · refine ⟨e2,true,?_,?_,?_⟩ <;> simp [e2,Equiv.swap_apply_def,h0,h1,h2]
  · refine ⟨e2,false,?_,?_,?_⟩ <;> simp [e2,Equiv.swap_apply_def,h0,h1,h2]
  · exact ⟨e,true,h0,h1,h2⟩
  · refine ⟨e1,true,?_,?_,?_⟩ <;> simp [e1,Equiv.swap_apply_def,h0,h1,h2]
  · exact False.elim (hnot true (by intro i; fin_cases i <;> assumption))

end WaveTurbulence.MoleProp
