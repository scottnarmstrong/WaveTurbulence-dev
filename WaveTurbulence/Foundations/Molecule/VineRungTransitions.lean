/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineClosedDoubleBlock
import Mathlib.Tactic

/-! # A membership transition at a full rung exhausts a connected block -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Losing one rail neighbor leaves at most three internal incidences. -/
theorem rung_degree_le_three (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {x y p q : V} (R : FourIncidences M x ![y,y,p,q])
    (hx : x ∈ S) (houtside : p ∉ S ∨ q ∉ S) : M.degIn S x≤3 := by
  have hd := fourIncidences_degree M hM R S hx
  simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,Nat.add_zero] at hd
  have hy := jointIndicator_le_one S y
  have hp := jointIndicator_le_one S p
  have hq := jointIndicator_le_one S q
  rcases houtside with hp' | hq'
  · have hz : jointIndicator S p=0 := by simp only [jointIndicator,hp',ite_false]
    omega
  · have hz : jointIndicator S q=0 := by simp only [jointIndicator,hq',ite_false]
    omega

omit [DecidableEq D] in
/-- At a selected non-joint block atom, all four incidences are internal. -/
theorem block_joint_of_degree_le_three (M : Molecule V D) {S : Finset V} {a b x : V}
    (hB : M.IsBlock S a b) (hx : x ∈ S) (hd : M.degIn S x≤3) : x=a ∨ x=b := by
  by_contra h
  have hn : x ≠ a ∧ x ≠ b := not_or.mp h
  have hh := hB.2.2.2.2.2.2.2.2.1 x hx hn.1 hn.2
  omega

/-- If both selected rung atoms lose a rail neighbor, they must be the two
joints. Connectivity then forces the entire block to be just that double pair. -/
theorem block_transition_eq_double_pair (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b x y p q r s : V} (hB : M.IsBlock S a b) (hC : GroupConnected M S)
    (Rx : FourIncidences M x ![y,y,p,q]) (Ry : FourIncidences M y ![x,x,r,s])
    (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y)
    (hox : p ∉ S ∨ q ∉ S) (hoy : r ∉ S ∨ s ∉ S) : S={x,y} := by
  have hxj := block_joint_of_degree_le_three M hB hx (rung_degree_le_three M hM Rx hx hox)
  have hyj := block_joint_of_degree_le_three M hB hy (rung_degree_le_three M hM Ry hy hoy)
  rcases hxj with hxa | hxb
  · subst x
    rcases hyj with hya | hyb
    · exact False.elim (hne hya.symm)
    · subst y
      exact connected_block_eq_double_pair M hB hC Rx.rung
  · subst x
    rcases hyj with hya | hyb
    · subst y
      simpa only [pair_comm] using connected_block_eq_double_pair M hB hC Ry.rung
    · exact False.elim (hne hyb.symm)

end WaveTurbulence.Vine
