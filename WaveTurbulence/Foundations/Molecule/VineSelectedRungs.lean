/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineEmptyRungs
import Mathlib.Tactic

/-! # Selected double rungs with a selected predecessor propagate selection -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- No atom of a block has internal degree three. -/
theorem block_degree_ne_three (M : Molecule V D) {A : Finset V} {a b x : V}
    (hB : M.IsBlock A a b) (hx : x ∈ A) : M.degIn A x ≠ 3 := by
  have hd := Mole.block_joint_degrees M hB
  by_cases ha : x=a
  · subst x; omega
  by_cases hb : x=b
  · subst x; omega
  have hh := hB.2.2.2.2.2.2.2.2.1 x hx ha hb
  omega

/-- With the doubled partner and predecessor selected, a full rung cannot
lose its successor: that would give the forbidden internal degree three. -/
theorem block_rung_next_mem (M : Molecule V D) (hM : M.IsMolecule)
    {A : Finset V} {a b x y p q : V} (hB : M.IsBlock A a b)
    (R : FourIncidences M x ![y,y,p,q]) (hx : x ∈ A) (hy : y ∈ A) (hp : p ∈ A) : q ∈ A := by
  by_contra hq
  have hd := fourIncidences_degree M hM R A hx
  have hn := block_degree_ne_three M hB hx
  have hy1 : jointIndicator A y=1 := by simp only [jointIndicator,hy,ite_true]
  have hp1 : jointIndicator A p=1 := by simp only [jointIndicator,hp,ite_true]
  have hq0 : jointIndicator A q=0 := by simp only [jointIndicator,hq,ite_false]
  simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,Nat.add_zero,hy1,hp1,hq0] at hd
  exact hn hd

/-- Once the first full pair and its predecessors are selected, selection
propagates through every full rung and the terminal pair, at any length. -/
theorem block_selected_fullRungSequence (M : Molecule V D) (hM : M.IsMolecule)
    {A : Finset V} {a b : V} (hB : M.IsBlock A a b) {n : ℕ} (Q : FullRungSequence M n)
    (hu0 : Q.u 0 ∈ A) (hv0 : Q.v 0 ∈ A) (hu1 : Q.u 1 ∈ A) (hv1 : Q.v 1 ∈ A) :
    ∀ i,i ≤ n+1 → Q.u i ∈ A ∧ Q.v i ∈ A := by
  have hh : ∀ t,t ≤ n → Q.u t ∈ A ∧ Q.v t ∈ A ∧ Q.u (t+1) ∈ A ∧ Q.v (t+1) ∈ A := by
    intro t
    induction t with
    | zero => intro _; exact ⟨hu0,hv0,hu1,hv1⟩
    | succ t ih =>
      intro ht
      have hp := ih (by omega)
      refine ⟨hp.2.2.1,hp.2.2.2,?_,?_⟩
      · apply block_rung_next_mem M hM hB (Q.upper (t+1) (by omega) ht) hp.2.2.1 hp.2.2.2
        simpa only [Nat.add_sub_cancel] using hp.1
      · apply block_rung_next_mem M hM hB (Q.lower (t+1) (by omega) ht) hp.2.2.2 hp.2.2.1
        simpa only [Nat.add_sub_cancel] using hp.2.1
  intro i hi
  by_cases hz : i=0
  · subst i
    exact ⟨hu0,hv0⟩
  · have he : i-1+1=i := by omega
    have hp := hh (i-1) (by omega)
    simpa only [he] using hp.2.2

end WaveTurbulence.Vine
