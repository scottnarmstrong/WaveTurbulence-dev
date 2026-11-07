/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.OneExitBound
import Mathlib.Tactic

/-! # An atom set attached by two bonds at one atom (DH23 ylem2, (Y1) case 3, L1952)

`Y` is attached to the rest by `x` (outgoing) and `y` (incoming), both ending at the same atom `w ∉ Y`. The removed
labels are those of the darts touching `Y`; they form the decorations of the molecule `aux`, obtained from `N` by
contracting every atom outside `Y` to one new atom `none` (and dropping the bonds outside `Y`). The new atom has
degree two, with the two exit bonds; its large gap is the large gap of `N` at `w` (DH23: "using Lemma A.3(1) and the
LG assumption at `v_{2n+1}`").
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- `Y` is attached by `x` (outgoing) and `y` (incoming), both at the same outside atom. -/
structure Pinch (N : Molecule V D) where
  Y : Finset V
  sub : Y ⊆ N.atoms
  x : D
  y : D
  cross : crossDarts N Y = {x, y}
  ne : x ≠ y
  same : N.atom (N.mate x) = N.atom (N.mate y)
  out_x : N.out x = true
  out_y : N.out y = false

namespace Pinch
variable {N : Molecule V D} (T : Pinch N)

def w : V := N.atom (N.mate T.x)

theorem x_mem : T.x ∈ crossDarts N T.Y := by rw [T.cross]; simp
theorem y_mem : T.y ∈ crossDarts N T.Y := by rw [T.cross]; simp
theorem atom_x : N.atom T.x ∈ T.Y := (mem_crossDarts.mp T.x_mem).1
theorem atom_y : N.atom T.y ∈ T.Y := (mem_crossDarts.mp T.y_mem).1
theorem w_notMem : T.w ∉ T.Y := (mem_crossDarts.mp T.x_mem).2

/-- The contracted molecule: the atoms of `Y` and one new atom `none` for the rest. -/
def aux : Molecule (Option V) (MoleProp.DeletedDart N T.Y) where
  atoms := insert none (T.Y.image some)
  atom z := if N.atom z.val ∈ T.Y then some (N.atom z.val) else none
  mate z := ⟨N.mate z.val, by
    have := z.property; rw [N.mate_mate]; tauto⟩
  out z := N.out z.val
  atom_mem z := by
    split_ifs with h
    · exact mem_insert_of_mem (mem_image_of_mem _ h)
    · exact mem_insert_self _ _
  mate_mate z := Subtype.ext (N.mate_mate z.val)
  mate_ne z h := N.mate_ne z.val (congrArg Subtype.val h)
  out_mate z := N.out_mate z.val

end Pinch
end WaveTurbulence.MoleProp4
