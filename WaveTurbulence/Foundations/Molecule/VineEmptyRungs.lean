/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRungTransitions
public import WaveTurbulence.Foundations.Molecule.VineRungPairIndices
import Mathlib.Tactic

/-! # Empty rung predecessors propagate through ladders of every length -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- Every atom selected in a block has internal degree at least two. -/
theorem block_degree_ge_two (M : Molecule V D) {A : Finset V} {a b x : V}
    (hB : M.IsBlock A a b) (hx : x ∈ A) : 2 ≤ M.degIn A x := by
  have hd := Mole.block_joint_degrees M hB
  by_cases hxa : x=a
  · subst x; omega
  by_cases hxb : x=b
  · subst x; omega
  have hh := hB.2.2.2.2.2.2.2.2.1 x hx hxa hxb
  omega

/-- A selected rung atom with an absent rail predecessor must include its
partner; otherwise it has at most one internal incidence. -/
theorem block_rung_partner_of_missing_rail (M : Molecule V D) (hM : M.IsMolecule)
    {A : Finset V} {a b x y p q : V} (hB : M.IsBlock A a b)
    (R : FourIncidences M x ![y,y,p,q]) (hx : x ∈ A) (hp : p ∉ A) : y ∈ A := by
  by_contra hy
  have hd := fourIncidences_degree M hM R A hx
  have hmin := block_degree_ge_two M hB hx
  have hmax := jointIndicator_le_one A q
  have hy0 : jointIndicator A y=0 := by simp only [jointIndicator,hy,ite_false]
  have hp0 : jointIndicator A p=0 := by simp only [jointIndicator,hp,ite_false]
  simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,Nat.add_zero,hy0,hp0] at hd
  omega

/-- TARGET subsetvc, empty-rung propagation: for any connected block larger
than a double bond, an absent predecessor pair forces the next full rung to
be absent. No lower bound on the total ladder length is needed. -/
theorem block_empty_predecessors (M : Molecule V D) (hM : M.IsMolecule)
    {A : Finset V} {a b x y p q r s : V} (hB : M.IsBlock A a b)
    (hC : GroupConnected M A) (hcard : 2<A.card)
    (Rx : FourIncidences M x ![y,y,p,q]) (Ry : FourIncidences M y ![x,x,r,s])
    (hne : x ≠ y) (hp : p ∉ A) (hr : r ∉ A) : x ∉ A ∧ y ∉ A := by
  have absurd_pair : A={x,y} → False := by
    intro he
    have hc := congrArg Finset.card he
    rw [card_pair hne] at hc
    omega
  have hxnot : x ∉ A := by
    intro hx
    have hy := block_rung_partner_of_missing_rail M hM hB Rx hx hp
    exact absurd_pair (block_transition_eq_double_pair M hM hB hC Rx Ry hx hy hne
      (Or.inl hp) (Or.inl hr))
  refine ⟨hxnot,?_⟩
  intro hy
  exact hxnot (block_rung_partner_of_missing_rail M hM hB Ry hy hr)

/-- All rungs are absent when the initial rail endpoints are absent.
This applies to arbitrary full sequences, including lengths one and two. -/
theorem block_empty_fullRungSequence (M : Molecule V D) (hM : M.IsMolecule)
    {A : Finset V} {a b : V} (hB : M.IsBlock A a b)
    (hC : GroupConnected M A) (hcard : 2<A.card) {n : ℕ} (Q : FullRungSequence M n)
    (hu0 : Q.u 0 ∉ A) (hv0 : Q.v 0 ∉ A) :
    ∀ i,1 ≤ i → i ≤ n → Q.u i ∉ A ∧ Q.v i ∉ A := by
  intro i hi
  induction i,hi using Nat.le_induction with
  | base =>
    intro hin
    apply block_empty_predecessors M hM hB hC hcard (Q.upper 1 le_rfl hin)
      (Q.lower 1 le_rfl hin) (Q.upper_ne_lower le_rfl hin le_rfl hin)
    · exact hu0
    · exact hv0
  | succ i hi ih =>
    intro hin
    have hprev := ih (by omega)
    apply block_empty_predecessors M hM hB hC hcard (Q.upper (i+1) (by omega) hin)
      (Q.lower (i+1) (by omega) hin) (Q.upper_ne_lower (by omega) hin (by omega) hin)
    · simpa only [Nat.add_sub_cancel] using hprev.1
    · simpa only [Nat.add_sub_cancel] using hprev.2

end WaveTurbulence.Vine
