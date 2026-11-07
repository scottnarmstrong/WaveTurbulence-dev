/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeBondEdits
import Mathlib.Tactic

/-! # Literal oriented and parallel multiplicity changes under reinsertion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp4
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

private theorem card_filter_sum (p : D ⊕ Bool → Prop) [DecidablePred p] :
    (univ.filter p).card = (univ.filter (fun x : D => p (.inl x))).card +
      (univ.filter (fun x : Bool => p (.inr x))).card := by
  have h : univ.filter p = (univ.filter (fun x : D => p (.inl x))).disjSum
      (univ.filter (fun x : Bool => p (.inr x))) := by
    ext x
    cases x <;> simp
  rw [h,card_disjSum]

/-- The new outgoing incidence occurs exactly at the first endpoint. -/
theorem addBond_outdeg (M : Molecule V D) (a b z : V) :
    (Mole.addBond M a b).outdeg z = M.outdeg z + (if a = z then 1 else 0) := by
  classical
  change ((univ.filter (fun x : D ⊕ Bool => (Mole.addBond M a b).atom x = z)).filter
    (fun x => (Mole.addBond M a b).out x = true)).card = _
  rw [filter_filter,card_filter_sum]
  change (univ.filter (fun x : D => M.atom x = z ∧ M.out x = true)).card +
    (univ.filter (fun x : Bool => (if x then a else b) = z ∧ x = true)).card = _
  rw [show (univ : Finset Bool) = {true,false} by decide]
  have hleft : (univ.filter (fun x : D => M.atom x = z ∧ M.out x = true)).card = M.outdeg z := by
    simp only [Molecule.outdeg,Molecule.dartsAt,filter_filter]
  rw [hleft]
  by_cases ha : a = z <;> simp [filter_insert,filter_singleton,ha]

/-- Parallel multiplicity increases by one exactly on the inserted pair. -/
theorem addBond_bondsBetween (M : Molecule V D) (a b u v : V) :
    (Mole.addBond M a b).bondsBetween u v = M.bondsBetween u v +
      (if s(a,b) = s(u,v) then 1 else 0) := by
  classical
  change ((univ.filter (fun x : D ⊕ Bool => (Mole.addBond M a b).out x = true)).filter
    (fun x => (Mole.addBond M a b).ends x = s(u,v))).card = _
  rw [filter_filter,card_filter_sum]
  change (univ.filter (fun x : D => M.out x = true ∧ M.ends x = s(u,v))).card +
    (univ.filter (fun x : Bool => x = true ∧
      s((if x then a else b),(if !x then a else b)) = s(u,v))).card = _
  have hleft : (univ.filter (fun x : D => M.out x = true ∧ M.ends x = s(u,v))).card = M.bondsBetween u v := by
    simp only [Molecule.bondsBetween,Molecule.bonds,filter_filter]
  rw [hleft,show (univ : Finset Bool) = {true,false} by decide]
  by_cases he : s(a,b) = s(u,v)
  · have h := Sym2.eq_iff.mp he
    simp [filter_insert,filter_singleton,he,h]
  · have h : ¬(a = u ∧ b = v ∨ a = v ∧ b = u) := by
      simpa only [Sym2.eq_iff] using he
    simp [filter_insert,filter_singleton,he,h]

end WaveTurbulence.MoleProp4
