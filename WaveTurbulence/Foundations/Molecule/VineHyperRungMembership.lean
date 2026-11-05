/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineBlockMarkers
public import WaveTurbulence.Foundations.Molecule.MoleculeHyperBlocks
import Mathlib.Tactic

/-! # A hyper-block cannot split even one full rung (TARGET subsetvc) -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Every selected hyper-block atom has internal degree at least three. -/
theorem hyperBlock_degree_ge_three (M : Molecule V D) {S : Finset V} {a b x : V}
    (hH : Mole.IsHyperBlock M S a b) (hx : x ∈ S) : 3 ≤ M.degIn S x := by
  obtain ⟨ha,hb,hint⟩ := Mole.hyperBlock_degrees M hH
  by_cases hxa : x=a
  · subst x; omega
  · by_cases hxb : x=b
    · subst x; omega
    · have hh := hint x hx hxa hxb
      omega

private theorem rung_partner_mem (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {x y prev next : V}
    (R : FourIncidences M x ![y,y,prev,next]) (hx : x ∈ S) (hd : 3 ≤ M.degIn S x) : y ∈ S := by
  by_contra hy
  have hh := fourIncidences_degree M hM R S hx
  have hy0 : jointIndicator S y=0 := by simp only [jointIndicator,hy,ite_false]
  simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,Nat.add_zero,hy0,Nat.zero_add] at hh
  have hprev := jointIndicator_le_one S prev
  have hnext := jointIndicator_le_one S next
  omega

/-- Each full rung has matched membership in a hyper-block, irrespective
of its position and the total ladder length. -/
theorem hyperBlock_rung_membership (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b x y p q r s : V} (hH : Mole.IsHyperBlock M S a b)
    (Rx : FourIncidences M x ![y,y,p,q]) (Ry : FourIncidences M y ![x,x,r,s]) :
    x ∈ S ↔ y ∈ S := by
  constructor
  · intro hx
    exact rung_partner_mem M hM Rx hx (hyperBlock_degree_ge_three M hH hx)
  · intro hy
    exact rung_partner_mem M hM Ry hy (hyperBlock_degree_ge_three M hH hy)

end WaveTurbulence.Vine
