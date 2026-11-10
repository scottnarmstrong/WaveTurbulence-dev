/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Degen.EvenDegreeCuts
public import WaveTurbulence.Foundations.FinalCount.WorldSelectedLadderDisjoint
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.ENat.Lattice
public import WaveTurbulence.Foundations.FinalCount.Degen.CircuitNormalization
import Mathlib.Tactic

/-! # Fixed-label degree-two degenerate removal in the all-even case -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A selected rung plus a selected rail already uses three half-edges. -/
theorem degree_ge_three_of_double_and_single (M : Molecule V D) {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hb : M.bondsBetween a b = 2) (hc : M.bondsBetween a c = 1) : 3 ≤ M.deg a := by
  have hn : a ∉ ({b,c} : Finset V) := by simp only [mem_insert,mem_singleton]; tauto
  have hh := sum_neighbor_bonds_le_degree M a {b,c} hn
  have hbc' : b ∉ ({c} : Finset V) := by simpa only [mem_singleton] using hbc
  rw [sum_insert hbc',sum_singleton,hb,hc] at hh
  exact hh

/-- Every atom in either rail of a genuine source ladder has degree at least three. -/
theorem sourceLadder_row_degree_ge_three (M : Molecule V D) {m : ℕ}
    {u v : Fin (m+1) → V} (hL : SourceLadder M u v) (j : Fin (m+1)) : 3 ≤ M.deg (u j) := by
  have hm := hL.1
  have hcross (i k : Fin (m+1)) : u i ≠ v k := by
    intro he
    have hh : (Sum.inl i : Fin (m+1) ⊕ Fin (m+1)) = Sum.inr k := hL.2.1 he
    cases hh
  have huinj : Function.Injective u := (Sum.elim_injective.mp hL.2.1).1
  by_cases hj : j.val < m
  · let t : Fin m := ⟨j.val,hj⟩
    have he : t.castSucc = j := Fin.ext rfl
    have hne : j ≠ t.succ := by
      intro hh
      have hv := congrArg Fin.val hh
      dsimp only [t] at hv
      simp only [Fin.val_succ] at hv
      omega
    apply degree_ge_three_of_double_and_single M (hcross j j) (fun hh => hne (huinj hh))
      (hcross t.succ j).symm (hL.2.2.2.1 j)
    simpa only [he] using (hL.2.2.2.2 t).1
  · let t : Fin m := ⟨m-1,by omega⟩
    have he : t.succ = j := by apply Fin.ext; dsimp only [t]; simp only [Fin.val_succ]; omega
    have hne : j ≠ t.castSucc := by
      intro hh
      have hv := congrArg Fin.val hh
      dsimp only [t] at hv
      simp only [Fin.val_castSucc] at hv
      omega
    apply degree_ge_three_of_double_and_single M (hcross j j) (fun hh => hne (huinj hh))
      (hcross t.castSucc j).symm (hL.2.2.2.1 j)
    rw [bondsBetween_comm, ← he]
    exact (hL.2.2.2.2 t).1

end WaveTurbulence.Degen
