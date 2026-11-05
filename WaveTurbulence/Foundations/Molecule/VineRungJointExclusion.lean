/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRungConstant
import Mathlib.Tactic

/-! # Non-double block joints cannot lie on long full-rung sequences -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- At a degree-two joint whose rung partner is selected, its two rung
darts exhaust the joint. Both rail neighbors must lie outside the block. -/
theorem rung_joint_neighbors_not_mem (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b x y p q : V} (hB : M.IsBlock S a b)
    (R : FourIncidences M x ![y,y,p,q]) (hj : x=a ∨ x=b) (hy : y ∈ S) : p ∉ S ∧ q ∉ S := by
  obtain ⟨ha,hb⟩ := Mole.block_joint_degrees M hB
  have hx : x ∈ S := by rcases hj with rfl | rfl; exact hB.2.1; exact hB.2.2.1
  have hdx : M.degIn S x=2 := by rcases hj with rfl | rfl; exact ha; exact hb
  have hd := fourIncidences_degree M hM R S hx
  simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,Nat.add_zero] at hd
  have hy1 := (jointIndicator_eq_one_iff S y).mpr hy
  constructor
  · intro hp
    have hp1 := (jointIndicator_eq_one_iff S p).mpr hp
    omega
  · intro hq
    have hq1 := (jointIndicator_eq_one_iff S q).mpr hq
    omega

/-- A connected block on more than two atoms has no joint among the full
rung atoms of a sequence with at least three rungs. -/
theorem block_fullRungSequence_no_joints (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (hB : M.IsBlock S a b) (hC : GroupConnected M S)
    (hcard : 2<S.card) {n : ℕ} (hn : 3 ≤ n) (R : FullRungSequence M n)
    (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    (R.u i ≠ a ∧ R.u i ≠ b) ∧ (R.v i ≠ a ∧ R.v i ≠ b) := by
  obtain ⟨j,hj,hjn,hji⟩ : ∃ j,1 ≤ j ∧ j ≤ n ∧ (j=i-1 ∨ j=i+1) := by
    by_cases h : i<n
    · exact ⟨i+1,by omega,by omega,Or.inr rfl⟩
    · exact ⟨i-1,by omega,by omega,Or.inl rfl⟩
  have hpair := block_fullRungSequence_membership M hM hB hn R i hi hin
  have hsame := block_fullRungSequence_constant M hM hB hC hcard hn R i hi hin j hj hjn
  have hu : ¬(R.u i=a ∨ R.u i=b) := by
    intro hjoint
    have hx : R.u i ∈ S := by rcases hjoint with h | h <;> rw [h]; exact hB.2.1; exact hB.2.2.1
    have hy := hpair.mp hx
    have hnot := rung_joint_neighbors_not_mem M hM hB (R.upper i hi hin) hjoint hy
    have hjmem := hsame.mp hx
    rcases hji with rfl | rfl
    · exact hnot.1 hjmem
    · exact hnot.2 hjmem
  have hv : ¬(R.v i=a ∨ R.v i=b) := by
    intro hjoint
    have hy : R.v i ∈ S := by rcases hjoint with h | h <;> rw [h]; exact hB.2.1; exact hB.2.2.1
    have hx := hpair.mpr hy
    have hnot := rung_joint_neighbors_not_mem M hM hB (R.lower i hi hin) hjoint hx
    have hjmem := (block_fullRungSequence_membership M hM hB hn R j hj hjn).mp (hsame.mp hx)
    rcases hji with rfl | rfl
    · exact hnot.1 hjmem
    · exact hnot.2 hjmem
  exact ⟨not_or.mp hu,not_or.mp hv⟩

end WaveTurbulence.Vine
