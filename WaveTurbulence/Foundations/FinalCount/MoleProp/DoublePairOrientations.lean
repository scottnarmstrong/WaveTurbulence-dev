/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairStars
import Mathlib.Tactic

/-! # The actual molecule caps produce all paired-star sign premises -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

private theorem outdeg_triple (M : Molecule V D) (a : V) {x y z : D}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hstar : M.dartsAt a = {x,y,z}) :
    M.outdeg a = (if M.out x = true then 1 else 0) + (if M.out y = true then 1 else 0) +
      (if M.out z = true then 1 else 0) := by
  have hh := sum_dartsAt_triple M a hxy hxz hyz hstar (fun q => if M.out q = true then (1 : ℕ) else 0)
  simpa only [sum_boole,Molecule.outdeg,Nat.cast_id] using hh

private theorem indeg_triple (M : Molecule V D) (a : V) {x y z : D}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hstar : M.dartsAt a = {x,y,z}) :
    M.indeg a = (if M.out x = false then 1 else 0) + (if M.out y = false then 1 else 0) +
      (if M.out z = false then 1 else 0) := by
  have hh := sum_dartsAt_triple M a hxy hxz hyz hstar (fun q => if M.out q = false then (1 : ℕ) else 0)
  simpa only [sum_boole,Molecule.indeg,Nat.cast_id] using hh

/-- The source two-in/two-out molecule caps exclude the two all-equal
sign patterns at an actual degree-three star. -/
theorem not_all_out_equal_of_triple_star (M : Molecule V D) (hM : M.IsMolecule)
    {a : V} (ha : a ∈ M.atoms) {x y r : D} (hxy : x ≠ y) (hxr : x ≠ r) (hyr : y ≠ r)
    (hstar : M.dartsAt a = {x,y,r}) : ¬(M.out x = M.out y ∧ M.out y = M.out r) := by
  have ho := (hM.1 a ha).1
  have hi := (hM.1 a ha).2
  rw [outdeg_triple M a hxy hxr hyr hstar] at ho
  rw [indeg_triple M a hxy hxr hyr hstar] at hi
  cases hx : M.out x <;> cases hy : M.out y <;> cases hr : M.out r <;> simp_all

private theorem outdeg_quadruple (M : Molecule V D) (a : V) {x y z t : D}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (ht : t ∉ ({x,y,z} : Finset D))
    (hstar : M.dartsAt a = {x,y,z,t}) :
    M.outdeg a = (if M.out x = true then 1 else 0) + (if M.out y = true then 1 else 0) +
      (if M.out z = true then 1 else 0) + (if M.out t = true then 1 else 0) := by
  have hh := sum_dartsAt_quadruple M a hxy hxz hyz ht hstar (fun q => if M.out q = true then (1 : ℕ) else 0)
  simpa only [sum_boole,Molecule.outdeg,Nat.cast_id] using hh

private theorem indeg_quadruple (M : Molecule V D) (a : V) {x y z t : D}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (ht : t ∉ ({x,y,z} : Finset D))
    (hstar : M.dartsAt a = {x,y,z,t}) :
    M.indeg a = (if M.out x = false then 1 else 0) + (if M.out y = false then 1 else 0) +
      (if M.out z = false then 1 else 0) + (if M.out t = false then 1 else 0) := by
  have hh := sum_dartsAt_quadruple M a hxy hxz hyz ht hstar (fun q => if M.out q = false then (1 : ℕ) else 0)
  simpa only [sum_boole,Molecule.indeg,Nat.cast_id] using hh

/-- The partner's actual four-incidence cap forces precisely the extra
sign used by SignedFive: equal rung signs give that sign, mixed rung
signs give the first endpoint's rail sign. -/
theorem extra_out_of_paired_star (M : Molecule V D) (hM : M.IsMolecule)
    {b : V} (hb : b ∈ M.atoms) {x y r s t : D}
    (hmxy : M.mate x ≠ M.mate y) (hmxs : M.mate x ≠ s) (hmys : M.mate y ≠ s)
    (ht : t ∉ ({M.mate x,M.mate y,s} : Finset D))
    (hstar : M.dartsAt b = {M.mate x,M.mate y,s,t}) (hout : M.out s = !M.out r) :
    M.out t = if M.out x = M.out y then M.out x else M.out r := by
  have ho := (hM.1 b hb).1
  have hi := (hM.1 b hb).2
  rw [outdeg_quadruple M b hmxy hmxs hmys ht hstar] at ho
  rw [indeg_quadruple M b hmxy hmxs hmys ht hstar] at hi
  rw [M.out_mate,M.out_mate,hout] at ho hi
  cases hx : M.out x <;> cases hy : M.out y <;> cases hr : M.out r <;> cases htout : M.out t <;> simp_all

end WaveTurbulence.MoleProp
