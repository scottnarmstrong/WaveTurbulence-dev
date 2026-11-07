/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.C5Vine
import Mathlib.Tactic

/-! # Prop 9.6, case (5): degrees and bond counts in terms of the bond multiset -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4

section
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- For a loop-free molecule, the degree of `v` is the number of bonds containing `v`. -/
theorem deg_eq_card_bonds (N : Molecule V D) (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) (v : V) :
    N.deg v = Multiset.card ((N.groupBonds N.atoms).filter (fun e => v ∈ e)) := by
  classical
  unfold Molecule.groupBonds
  rw [Multiset.filter_map, Multiset.card_map]
  rw [← Finset.filter_val, Finset.card_val, Finset.filter_filter]
  unfold Molecule.deg Molecule.dartsAt
  have hg : ∀ x, N.atom x = v → (if N.out x = true then x else N.mate x) ∈
      Finset.univ.filter (fun x => (N.out x = true ∧ N.InGroup N.atoms x) ∧ v ∈ N.ends x) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with ho
    · exact ⟨⟨ho, N.atom_mem _, N.atom_mem _⟩, by simp [Molecule.ends, hx]⟩
    · have ho' : N.out (N.mate x) = true := by rw [N.out_mate]; simpa using ho
      exact ⟨⟨ho', N.atom_mem _, N.atom_mem _⟩, by simp [Molecule.ends, N.mate_mate, hx]⟩
  refine Finset.card_bij (fun x _ => if N.out x = true then x else N.mate x) ?_ ?_ ?_
  · intro x hx
    exact hg x (by simpa using hx)
  · intro x hx y hy hxy
    have hx' : N.atom x = v := by simpa using hx
    have hy' : N.atom y = v := by simpa using hy
    by_cases hox : N.out x = true <;> by_cases hoy : N.out y = true
    · simpa [hox, hoy] using hxy
    · exfalso
      rw [if_pos hox, if_neg hoy] at hxy
      apply hloop y; rw [← hxy, hx', hy']
    · exfalso
      rw [if_neg hox, if_pos hoy] at hxy
      apply hloop x; rw [hxy, hx', hy']
    · rw [if_neg hox, if_neg hoy] at hxy
      exact Mole.mate_injective N hxy
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨⟨ho, _⟩, hv⟩ := hy
    have hv' : v = N.atom y ∨ v = N.atom (N.mate y) := by simpa [Molecule.ends, Sym2.mem_iff] using hv
    rcases hv' with hv | hv
    · exact ⟨y, by simp [hv], by simp [ho]⟩
    · refine ⟨N.mate y, by simp [hv], ?_⟩
      have : ¬ N.out (N.mate y) = true := by rw [N.out_mate, ho]; simp
      rw [if_neg this, N.mate_mate]

end
end WaveTurbulence.FinalCountG8
