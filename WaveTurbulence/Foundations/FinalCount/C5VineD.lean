/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.C5VineC
import Mathlib.Tactic

/-! # Prop 9.6, case (5): bond counts at an atom with exactly two darts -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4

section
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The bond count between `w` and `q`, for an atom `w` with exactly two darts `x1, x2`. -/
theorem bb_two_darts (M : Molecule V D) (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) {w : V} {x1 x2 : D}
    (h1 : M.atom x1 = w) (h2 : M.atom x2 = w) (hne : x1 ≠ x2) (hall : ∀ x, M.atom x = w → x = x1 ∨ x = x2)
    (q : V) :
    M.bondsBetween w q = (if M.atom (M.mate x1) = q then 1 else 0) + (if M.atom (M.mate x2) = q then 1 else 0) := by
  classical
  by_cases hq : q = w
  · subst hq
    rw [bondsBetween_self_eq_zero hloop]
    have a1 : M.atom (M.mate x1) ≠ q := fun h => hloop x1 (by rw [h1, h])
    have a2 : M.atom (M.mate x2) ≠ q := fun h => hloop x2 (by rw [h2, h])
    rw [if_neg a1, if_neg a2]
  have : M.bondsBetween w q = (({x1, x2} : Finset D).filter (fun x => M.atom (M.mate x) = q)).card := by
    unfold Molecule.bondsBetween Molecule.bonds
    symm
    refine Finset.card_bij (fun x _ => if M.out x = true then x else M.mate x) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hx
      obtain ⟨hx12, hxq⟩ := hx
      have hxw : M.atom x = w := by rcases hx12 with rfl | rfl <;> assumption
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases ho : M.out x = true
      · rw [if_pos ho]; exact ⟨ho, by simp [Molecule.ends, hxw, hxq]⟩
      · have ho' : M.out (M.mate x) = true := by rw [M.out_mate]; simpa using ho
        rw [if_neg ho]
        refine ⟨ho', ?_⟩
        simp [Molecule.ends, M.mate_mate, hxw, hxq, Sym2.eq_swap]
    · intro x hx y hy hxy
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hx hy
      have hxw : M.atom x = w := by rcases hx.1 with rfl | rfl <;> assumption
      have hyw : M.atom y = w := by rcases hy.1 with rfl | rfl <;> assumption
      by_cases hox : M.out x = true <;> by_cases hoy : M.out y = true
      · simpa [hox, hoy] using hxy
      · exfalso; rw [if_pos hox, if_neg hoy] at hxy
        apply hloop y; rw [← hxy, hxw, hyw]
      · exfalso; rw [if_neg hox, if_pos hoy] at hxy
        apply hloop x; rw [hxy, hxw, hyw]
      · rw [if_neg hox, if_neg hoy] at hxy
        exact Mole.mate_injective M hxy
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      obtain ⟨ho, hends⟩ := hy
      have hends' : M.atom y = w ∧ M.atom (M.mate y) = q ∨ M.atom y = q ∧ M.atom (M.mate y) = w := by
        have : s(M.atom y, M.atom (M.mate y)) = s(w, q) := hends
        rcases Sym2.eq_iff.mp this with h | h
        · exact Or.inl h
        · exact Or.inr h
      rcases hends' with ⟨hw, hqq⟩ | ⟨hqq, hw⟩
      · refine ⟨y, ?_, by simp [ho]⟩
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨hall y hw, hqq⟩
      · refine ⟨M.mate y, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          refine ⟨hall _ hw, by rw [M.mate_mate]; exact hqq⟩
        · have : ¬ M.out (M.mate y) = true := by rw [M.out_mate, ho]; simp
          rw [if_neg this, M.mate_mate]
  rw [this, Finset.filter_insert, Finset.filter_singleton]
  by_cases a1 : M.atom (M.mate x1) = q <;> by_cases a2 : M.atom (M.mate x2) = q <;> simp [a1, a2, hne]

end
end WaveTurbulence.FinalCountG8
