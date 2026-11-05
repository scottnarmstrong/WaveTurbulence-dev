/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineAssembleIncidences
public import WaveTurbulence.Foundations.Molecule.VineThinEmptyPairs
import Mathlib.Tactic

/-! # Selection propagates across the doubled side triangle -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Two distinct joints joined by a double pair exhaust a connected block,
regardless of which of the two ordered joint names they carry. -/
theorem block_eq_pair_of_joint_double (M : Molecule V D) {A : Finset V} {a b x y : V}
    (hB : M.IsBlock A a b) (hC : GroupConnected M A) (R : TwoIncidences M x y)
    (hne : x ≠ y) (hxj : x=a ∨ x=b) (hyj : y=a ∨ y=b) : A={x,y} := by
  rcases hxj with rfl | rfl <;> rcases hyj with rfl | rfl
  · exact False.elim (hne rfl)
  · exact connected_block_eq_double_pair M hB hC R
  · simpa only [pair_comm] using connected_block_eq_double_pair M hB hC R.mates
  · exact False.elim (hne rfl)

/-- A connected block larger than a double bond containing the center of
a triangle with two doubled sides contains both other triangle atoms. -/
theorem block_double_triangle_corners_mem (M : Molecule V D) (hM : M.IsMolecule)
    {A : Finset V} {a b x y z : V} (hB : M.IsBlock A a b) (hC : GroupConnected M A)
    (hcard : 2<A.card) (Ry : TwoIncidences M x y) (Rz : TwoIncidences M x z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hAdj : M.Adj y z) (hx : x ∈ A) :
    y ∈ A ∧ z ∈ A := by
  have R4 := FourIncidences.ofTwoPairs Ry Rz hyz
  have hsome : y ∈ A ∨ z ∈ A := by
    by_contra hh
    have hn : y ∉ A ∧ z ∉ A := not_or.mp hh
    have hd := fourIncidences_degree M hM R4 A hx
    have hmin := block_degree_ge_two M hB hx
    have hy0 : jointIndicator A y=0 := by simp only [jointIndicator,hn.1,ite_false]
    have hz0 : jointIndicator A z=0 := by simp only [jointIndicator,hn.2,ite_false]
    simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Fin.sum_univ_zero,Nat.add_zero,hy0,hz0] at hd
    omega
  have absurd_pair {p q : V} (hne : p ≠ q) (he : A={p,q}) : False := by
    have hc := congrArg Finset.card he
    rw [card_pair hne] at hc
    omega
  by_cases hy : y ∈ A
  · refine ⟨hy,?_⟩
    by_contra hz
    have hxj := block_split_double_is_joint M hM hB Rz hx hz
    have hyj := block_joint_of_external_neighbor M hM hB hy hz hAdj
    exact absurd_pair hxy (block_eq_pair_of_joint_double M hB hC Ry hxy hxj hyj)
  · have hz := hsome.resolve_left hy
    have hxj := block_split_double_is_joint M hM hB Ry hx hy
    have hzj := block_joint_of_external_neighbor M hM hB hz hy (Mole.adj_symmetric M hAdj)
    exact False.elim (absurd_pair hxz (block_eq_pair_of_joint_double M hB hC Rz hxz hxj hzj))

end WaveTurbulence.Vine
