/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineFourIncidences
public import WaveTurbulence.Foundations.Molecule.VineDoublePairClosure
public import WaveTurbulence.Foundations.Molecule.VineRungSequences
import Mathlib.Tactic

/-! # The doubled neighbor in a full rail row is unique -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- In a complete row [w,w,p,q] with distinct rail neighbors p and q,
any two parallel incidences must go to the doubled neighbor w. -/
theorem four_row_double_neighbor_unique (M : Molecule V D) (hM : M.IsMolecule)
    {v w p q z : V} (R : FourIncidences M v ![w,w,p,q]) (hpq : p ≠ q)
    (T : TwoIncidences M v z) : z=w := by
  have find (i : Fin 2) : ∃ j : Fin 4,R.dart j=T.dart i := by
    have hi : T.dart i ∈ M.dartsAt v := (Mole.mem_dartsAt M v _).mpr (T.atom_eq i)
    rw [← fourIncidences_image M hM R] at hi
    obtain ⟨j,_hj,he⟩ := mem_image.mp hi
    exact ⟨j,he⟩
  obtain ⟨j0,h0⟩ := find 0
  obtain ⟨j1,h1⟩ := find 1
  have hne : j0 ≠ j1 := by
    intro he
    have hh := T.injective (h0.symm.trans ((congrArg R.dart he).trans h1))
    have hv := congrArg Fin.val hh
    norm_num at hv
  have hn0 : ![w,w,p,q] j0=z := by rw [← R.neighbor_eq,h0,T.neighbor_eq]
  have hn1 : ![w,w,p,q] j1=z := by rw [← R.neighbor_eq,h1,T.neighbor_eq]
  fin_cases j0 <;> fin_cases j1
  all_goals first
    | exact hn0.symm
    | exact hn1.symm
    | exact False.elim (hne rfl)
    | exact False.elim (hpq (hn0.trans hn1.symm))
    | exact False.elim (hpq (hn1.trans hn0.symm))

/-- On any upper full rung, the only possible doubled neighbor is its
actual lower partner, including rungs next to either old port. -/
theorem FullRungSequence.upper_double_neighbor (M : Molecule V D) (hM : M.IsMolecule)
    {n : ℕ} (Q : FullRungSequence M n)
    (hd : Function.Injective (fun i : Fin (n+2) => Q.u i.1))
    (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) {z : V} (T : TwoIncidences M (Q.u i) z) : z=Q.v i := by
  apply four_row_double_neighbor_unique M hM (Q.upper i hi hin) _ T
  intro he
  have hh := hd (a₁ := ⟨i-1,by omega⟩) (a₂ := ⟨i+1,by omega⟩) he
  have hv := congrArg Fin.val hh
  change i-1=i+1 at hv
  omega

/-- The symmetric lower-row uniqueness statement. -/
theorem FullRungSequence.lower_double_neighbor (M : Molecule V D) (hM : M.IsMolecule)
    {n : ℕ} (Q : FullRungSequence M n)
    (hd : Function.Injective (fun i : Fin (n+2) => Q.v i.1))
    (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) {z : V} (T : TwoIncidences M (Q.v i) z) : z=Q.u i := by
  apply four_row_double_neighbor_unique M hM (Q.lower i hi hin) _ T
  intro he
  have hh := hd (a₁ := ⟨i-1,by omega⟩) (a₂ := ⟨i+1,by omega⟩) he
  have hv := congrArg Fin.val hh
  change i-1=i+1 at hv
  omega

end WaveTurbulence.Vine
