/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.CoreGraph
import Mathlib.Tactic

/-! # A set attached by two bonds (any ends, any directions)

`Exits2 N`: `Y` is attached to the rest by exactly two darts `x ≠ y` leaving `Y`. Copy of MOLEPROP4-T `TwoExit`
without the `far`/direction fields (the dart classification and the straddle lemma never use them).
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

structure Exits2 (N : Molecule V D) where
  Y : Finset V
  sub : Y ⊆ N.atoms
  x : D
  y : D
  cross : crossDarts N Y = {x, y}
  ne : x ≠ y

namespace Exits2
variable {N : Molecule V D} (T : Exits2 N)

theorem x_mem : T.x ∈ crossDarts N T.Y := by rw [T.cross]; simp
theorem y_mem : T.y ∈ crossDarts N T.Y := by rw [T.cross]; simp

theorem atom_x : N.atom T.x ∈ T.Y := (mem_crossDarts.mp T.x_mem).1
theorem atom_y : N.atom T.y ∈ T.Y := (mem_crossDarts.mp T.y_mem).1

/-- A dart from `Y` to its complement is `x` or `y`. -/
theorem eq_of_cross {z : D} (h1 : N.atom z ∈ T.Y) (h2 : N.atom (N.mate z) ∉ T.Y) : z = T.x ∨ z = T.y := by
  have hz : z ∈ crossDarts N T.Y := mem_crossDarts.mpr ⟨h1, h2⟩
  rw [T.cross] at hz
  simpa using hz

/-- A dart from the complement into `Y` is `mate x` or `mate y`. -/
theorem eq_of_cross' {z : D} (h1 : N.atom z ∉ T.Y) (h2 : N.atom (N.mate z) ∈ T.Y) :
    z = N.mate T.x ∨ z = N.mate T.y := by
  have h := T.eq_of_cross (z := N.mate z) h2 (by rw [N.mate_mate]; exact h1)
  rcases h with h | h
  · left; rw [← h, N.mate_mate]
  · right; rw [← h, N.mate_mate]

/-- **Dart classification**: every dart is inside `Y`, outside `Y`, or one of the four exit darts. -/
theorem dart_cases (z : D) :
    (N.atom z ∈ T.Y ∧ N.atom (N.mate z) ∈ T.Y) ∨ (N.atom z ∉ T.Y ∧ N.atom (N.mate z) ∉ T.Y) ∨
      z = T.x ∨ z = T.y ∨ z = N.mate T.x ∨ z = N.mate T.y := by
  by_cases h1 : N.atom z ∈ T.Y <;> by_cases h2 : N.atom (N.mate z) ∈ T.Y
  · exact Or.inl ⟨h1, h2⟩
  · rcases T.eq_of_cross h1 h2 with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases T.eq_of_cross' h1 h2 with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · exact Or.inr (Or.inl ⟨h1, h2⟩)

theorem mate_x_ne_mate_y : N.mate T.x ≠ N.mate T.y := by
  intro h; apply T.ne; have := congrArg N.mate h; rwa [N.mate_mate, N.mate_mate] at this

/-- A cell of `N` meeting `Y` and its complement contains the atom of an exit. -/
theorem straddle_mem_exit {S : Finset V} (hS : MoleProp.IsLadderCell N S) (hin : ∃ a ∈ S, a ∈ T.Y)
    (hout : ∃ a ∈ S, a ∉ T.Y) : N.atom T.x ∈ S ∨ N.atom T.y ∈ S := by
  obtain ⟨u, v, hL, rfl⟩ := hS
  -- a bond between an atom of `Y` and one outside starts at an exit atom
  have cross : ∀ a b, a ∈ T.Y → b ∉ T.Y → 0 < N.bondsBetween a b → a = N.atom T.x ∨ a = N.atom T.y := by
    intro a b ha hb hpos
    have hab : a ≠ b := fun h => hb (h ▸ ha)
    rw [← Degen.card_neighborDarts N hab] at hpos
    obtain ⟨z, hz⟩ := card_pos.mp hpos
    obtain ⟨hza, hzb⟩ := (Degen.mem_neighborDarts N a b z).mp hz
    rcases T.eq_of_cross (z := z) (hza ▸ ha) (hzb ▸ hb) with rfl | rfl
    · exact Or.inl hza.symm
    · exact Or.inr hza.symm
  have hmem : ∀ j, u j ∈ Molecule.ladderAtoms u v ∧ v j ∈ Molecule.ladderAtoms u v := fun j =>
    ⟨mem_union_left _ (mem_image_of_mem _ (mem_univ j)), mem_union_right _ (mem_image_of_mem _ (mem_univ j))⟩
  have pick : ∀ a b, a ∈ Molecule.ladderAtoms u v → a ∈ T.Y → b ∉ T.Y → 0 < N.bondsBetween a b →
      N.atom T.x ∈ Molecule.ladderAtoms u v ∨ N.atom T.y ∈ Molecule.ladderAtoms u v := by
    intro a b haS ha hb hp
    rcases cross a b ha hb hp with rfl | rfl
    · exact Or.inl haS
    · exact Or.inr haS
  obtain ⟨_, _, _, hrung, hrail⟩ := hL
  obtain ⟨su, sv, _⟩ := hrail 0
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at su sv
  have bc := fun a b => Degen.bondsBetween_comm N a b
  have hS4 : ∀ z, z ∈ Molecule.ladderAtoms u v ↔ z = u 0 ∨ z = u 1 ∨ z = v 0 ∨ z = v 1 := by
    intro z
    simp only [Molecule.ladderAtoms, mem_union, mem_image, mem_univ, true_and]
    constructor
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩) <;> fin_cases i <;> simp
    · rintro (rfl | rfl | rfl | rfl)
      exacts [Or.inl ⟨0, rfl⟩, Or.inl ⟨1, rfl⟩, Or.inr ⟨0, rfl⟩, Or.inr ⟨1, rfl⟩]
  -- check every bond of the cell
  have hpos2 : ∀ j, 0 < N.bondsBetween (u j) (v j) := fun j => by rw [hrung j]; norm_num
  by_contra hno
  push Not at hno
  have nocross : ∀ a b, a ∈ Molecule.ladderAtoms u v → b ∈ Molecule.ladderAtoms u v → 0 < N.bondsBetween a b →
      (a ∈ T.Y ↔ b ∈ T.Y) := by
    intro a b ha hb hp
    by_contra hiff
    by_cases haY : a ∈ T.Y
    · have hbY : b ∉ T.Y := fun h => hiff ⟨fun _ => h, fun _ => haY⟩
      rcases pick a b ha haY hbY hp with h | h
      exacts [hno.1 h, hno.2 h]
    · have hbY : b ∈ T.Y := by by_contra h; exact hiff ⟨fun h' => absurd h' haY, fun h' => absurd h' h⟩
      rcases pick b a hb hbY haY (by rw [bc]; exact hp) with h | h
      exacts [hno.1 h, hno.2 h]
  have e00 := nocross _ _ (hmem 0).1 (hmem 0).2 (hpos2 0)
  have e11 := nocross _ _ (hmem 1).1 (hmem 1).2 (hpos2 1)
  have eu := nocross _ _ (hmem 0).1 (hmem 1).1 (by rw [su]; norm_num)
  obtain ⟨a, haS, haY⟩ := hin
  obtain ⟨b, hbS, hbY⟩ := hout
  rw [hS4] at haS hbS
  rcases haS with rfl | rfl | rfl | rfl <;> rcases hbS with rfl | rfl | rfl | rfl <;> tauto

end Exits2
end WaveTurbulence.FinalCountG8
