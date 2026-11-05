/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineHyperRungMembership
public import WaveTurbulence.Foundations.Molecule.VineRungTransitions
import Mathlib.Tactic

/-! # Hyper-block membership transitions consume both joints -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A selected hyper-block atom of degree at most three is a joint. -/
theorem hyperBlock_joint_of_degree_le_three (M : Molecule V D) {S : Finset V} {a b x : V}
    (hH : Mole.IsHyperBlock M S a b) (hx : x ∈ S) (hd : M.degIn S x ≤ 3) : x=a ∨ x=b := by
  by_contra h
  have hn : x ≠ a ∧ x ≠ b := not_or.mp h
  have hh := (Mole.hyperBlock_degrees M hH).2.2 x hx hn.1 hn.2
  omega

/-- At a hyper-block transition, the selected rung pair is exactly the
joint pair. Hence transitions on disjoint rung pairs cannot both occur. -/
theorem hyperBlock_transition_joints (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b x y p q r s : V} (hH : Mole.IsHyperBlock M S a b)
    (Rx : FourIncidences M x ![y,y,p,q]) (Ry : FourIncidences M y ![x,x,r,s])
    (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y)
    (hox : p ∉ S ∨ q ∉ S) (hoy : r ∉ S ∨ s ∉ S) :
    ({x,y} : Finset V)={a,b} := by
  have hxj := hyperBlock_joint_of_degree_le_three M hH hx (rung_degree_le_three M hM Rx hx hox)
  have hyj := hyperBlock_joint_of_degree_le_three M hH hy (rung_degree_le_three M hM Ry hy hoy)
  rcases hxj with rfl | rfl <;> rcases hyj with rfl | rfl
  · exact False.elim (hne rfl)
  · rfl
  · exact pair_comm _ _
  · exact False.elim (hne rfl)

/-- A selected full rung in a hyper-block cannot lose both rail neighbors:
that would leave only its two doubled-rung incidences. -/
theorem hyperBlock_rung_not_isolated (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b x y p q : V} (hH : Mole.IsHyperBlock M S a b)
    (R : FourIncidences M x ![y,y,p,q]) (hx : x ∈ S) : p ∈ S ∨ q ∈ S := by
  by_contra hh
  have hn : p ∉ S ∧ q ∉ S := not_or.mp hh
  have hd := fourIncidences_degree M hM R S hx
  have hmin := hyperBlock_degree_ge_three M hH hx
  have hmax := jointIndicator_le_one S y
  have hp : jointIndicator S p=0 := by simp only [jointIndicator,hn.1,ite_false]
  have hq : jointIndicator S q=0 := by simp only [jointIndicator,hn.2,ite_false]
  simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,Nat.add_zero,hp,hq] at hd
  omega

end WaveTurbulence.Vine
