/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.Piece
import Mathlib.Tactic

/-! # An atom set attached to the rest by exactly two bonds

The removed part of a (Y) sequence ending in (Y2) (DH23 L1929, Figure YOper) is attached to the rest of the molecule
by exactly two single bonds, `ℓ₁` from `v_{2n-1}` and `ℓ₂` from `v_{2n}`, whose far ends `v_{2n+1} ≠ v_{2n+2}` are
joined by the new bond. `TwoExit` records this for an arbitrary atom set `Y`: the darts leaving `Y` are exactly `x`
(outgoing, `Y → c`) and `y` (incoming, `d → Y`), with `c ≠ d`. The orientation is normalized (`x` outgoing); DH23's
"matching the directions of the removed single bonds" is then the new bond `d → c`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- `Y` is attached by exactly two bonds: `x` leaves `Y` outgoing towards `c`, `y` enters `Y` from `d ≠ c`. -/
structure TwoExit (N : Molecule V D) where
  Y : Finset V
  sub : Y ⊆ N.atoms
  x : D
  y : D
  cross : crossDarts N Y = {x, y}
  ne : x ≠ y
  far : N.atom (N.mate x) ≠ N.atom (N.mate y)
  out_x : N.out x = true
  out_y : N.out y = false

namespace TwoExit
variable {N : Molecule V D} (T : TwoExit N)

/-- The far end of the outgoing exit. -/
def c : V := N.atom (N.mate T.x)
/-- The far end of the incoming exit. -/
def d : V := N.atom (N.mate T.y)

theorem x_mem : T.x ∈ crossDarts N T.Y := by rw [T.cross]; simp
theorem y_mem : T.y ∈ crossDarts N T.Y := by rw [T.cross]; simp

theorem atom_x : N.atom T.x ∈ T.Y := (mem_crossDarts.mp T.x_mem).1
theorem atom_y : N.atom T.y ∈ T.Y := (mem_crossDarts.mp T.y_mem).1
theorem c_notMem : T.c ∉ T.Y := (mem_crossDarts.mp T.x_mem).2
theorem d_notMem : T.d ∉ T.Y := (mem_crossDarts.mp T.y_mem).2
theorem c_ne_d : T.c ≠ T.d := T.far
theorem c_mem : T.c ∈ N.atoms \ T.Y := mem_sdiff.mpr ⟨N.atom_mem _, T.c_notMem⟩
theorem d_mem : T.d ∈ N.atoms \ T.Y := mem_sdiff.mpr ⟨N.atom_mem _, T.d_notMem⟩

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

/-- The removed darts at a surviving atom `v`: `mate x` at `c`, `mate y` at `d`, nothing elsewhere. -/
theorem removedDartsAt_eq {v : V} (hv : v ∉ T.Y) :
    Degen.removedDartsAt N T.Y v =
      (if v = T.c then {N.mate T.x} else ∅) ∪ (if v = T.d then {N.mate T.y} else ∅) := by
  ext z
  simp only [Degen.removedDartsAt, Molecule.dartsAt, mem_filter, mem_univ, true_and, mem_union]
  constructor
  · rintro ⟨hz, hzY⟩
    rcases T.eq_of_cross' (z := z) (by rw [hz]; exact hv) hzY with rfl | rfl
    · left; simp [show v = T.c from hz.symm]
    · right; simp [show v = T.d from hz.symm]
  · rintro (h | h)
    · split_ifs at h with hc
      · rw [mem_singleton.mp h]; exact ⟨hc ▸ rfl, by rw [N.mate_mate]; exact T.atom_x⟩
      · simp at h
    · split_ifs at h with hd
      · rw [mem_singleton.mp h]; exact ⟨hd ▸ rfl, by rw [N.mate_mate]; exact T.atom_y⟩
      · simp at h

/-- The darts of `N` at atoms of `Y`: internal ones and the exits. -/
theorem atom_mem_Y_cases {z : D} (hz : N.atom z ∈ T.Y) :
    N.atom (N.mate z) ∈ T.Y ∨ z = T.x ∨ z = T.y := by
  by_cases h : N.atom (N.mate z) ∈ T.Y
  · exact Or.inl h
  · exact Or.inr (T.eq_of_cross hz h)

end TwoExit
end WaveTurbulence.MoleProp4
