/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineEmptyRungs
import Mathlib.Tactic

/-! # Empty rung propagation from the opposite end of a ladder -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The partner is selected when a selected rung atom loses its successor. -/
theorem block_rung_partner_of_missing_successor (M : Molecule V D) (hM : M.IsMolecule)
    {A : Finset V} {a b x y p q : V} (hB : M.IsBlock A a b)
    (R : FourIncidences M x ![y,y,p,q]) (hx : x ∈ A) (hq : q ∉ A) : y ∈ A := by
  by_contra hy
  have hd := fourIncidences_degree M hM R A hx
  have hmin := block_degree_ge_two M hB hx
  have hmax := jointIndicator_le_one A p
  have hy0 : jointIndicator A y=0 := by simp only [jointIndicator,hy,ite_false]
  have hq0 : jointIndicator A q=0 := by simp only [jointIndicator,hq,ite_false]
  simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,Nat.add_zero,hy0,hq0] at hd
  omega

/-- Empty successor pairs propagate backwards without a ladder-length bound. -/
theorem block_empty_successors (M : Molecule V D) (hM : M.IsMolecule)
    {A : Finset V} {a b x y p q r s : V} (hB : M.IsBlock A a b)
    (hC : GroupConnected M A) (hcard : 2<A.card)
    (Rx : FourIncidences M x ![y,y,p,q]) (Ry : FourIncidences M y ![x,x,r,s])
    (hne : x ≠ y) (hq : q ∉ A) (hs : s ∉ A) : x ∉ A ∧ y ∉ A := by
  have absurd_pair : A={x,y} → False := by
    intro he
    have hc := congrArg Finset.card he
    rw [card_pair hne] at hc
    omega
  have hxnot : x ∉ A := by
    intro hx
    have hy := block_rung_partner_of_missing_successor M hM hB Rx hx hq
    exact absurd_pair (block_transition_eq_double_pair M hM hB hC Rx Ry hx hy hne
      (Or.inr hq) (Or.inr hs))
  refine ⟨hxnot,?_⟩
  intro hy
  exact hxnot (block_rung_partner_of_missing_successor M hM hB Ry hy hs)

/-- All rungs are absent when the terminal rail endpoints are absent. -/
theorem block_empty_fullRungSequence_reverse (M : Molecule V D) (hM : M.IsMolecule)
    {A : Finset V} {a b : V} (hB : M.IsBlock A a b)
    (hC : GroupConnected M A) (hcard : 2<A.card) {n : ℕ} (Q : FullRungSequence M n)
    (huN : Q.u (n+1) ∉ A) (hvN : Q.v (n+1) ∉ A) :
    ∀ i,1 ≤ i → i ≤ n → Q.u i ∉ A ∧ Q.v i ∉ A := by
  have hh : ∀ t,t ≤ n → Q.u (n+1-t) ∉ A ∧ Q.v (n+1-t) ∉ A := by
    intro t
    induction t with
    | zero => intro _; exact ⟨huN,hvN⟩
    | succ t ih =>
      intro ht
      have hprev := ih (by omega)
      let j := n+1-(t+1)
      have hj : 1 ≤ j := by dsimp only [j]; omega
      have hjn : j ≤ n := by dsimp only [j]; omega
      have hnext : j+1=n+1-t := by dsimp only [j]; omega
      apply block_empty_successors M hM hB hC hcard (Q.upper j hj hjn)
        (Q.lower j hj hjn) (Q.upper_ne_lower hj hjn hj hjn)
      · simpa only [hnext] using hprev.1
      · simpa only [hnext] using hprev.2
  intro i hi hin
  have hindex : n+1-(n+1-i)=i := by omega
  simpa only [hindex] using hh (n+1-i) (by omega)

end WaveTurbulence.Vine
