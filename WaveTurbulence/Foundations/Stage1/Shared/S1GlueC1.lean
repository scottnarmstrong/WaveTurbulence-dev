/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.LFConstruction
import Mathlib.Tactic

/-!
# Gluing a template couple into a layered base (address level)

The translation `couplePort` sends the two regions below `a`, `b` to the regions below `aT`, `bT`
(relative addresses are kept).  `glueAt` is the layer function of the glued garden: the template's
layers inside the regions, the base's layers outside.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ}

/-- Translation of the two regions below `a`, `b` to those below `aT`, `bT`. -/
@[expose] def couplePort (a b aT bT : Fin w × Path) (z : Fin w × Path) : Fin w × Path :=
  if Under a z then addrExt aT (z.2.drop a.2.length)
  else if Under b z then addrExt bT (z.2.drop b.2.length) else z

theorem couplePort_a (a b aT bT : Fin w × Path) (hab : Indep a b) (q : Path) :
    couplePort a b aT bT (addrExt a q) = addrExt aT q := by
  unfold couplePort
  simp only [under_ext a q, ↓reduceIte]
  simp [addrExt]

theorem couplePort_b (a b aT bT : Fin w × Path) (hab : Indep a b) (q : Path) :
    couplePort a b aT bT (addrExt b q) = addrExt bT q := by
  have h : ¬ Under a (addrExt b q) := by
    intro h
    rcases under_total h (under_ext b q) |>.symm with h2 | h2
    · exact hab.2 h2
    · exact hab.1 h2
  unfold couplePort
  simp only [h, under_ext b q, ↓reduceIte]
  simp [addrExt]

theorem couplePort_out (a b aT bT : Fin w × Path) {z : Fin w × Path} (h : ¬ InRegion a b z) :
    couplePort a b aT bT z = z := by
  unfold couplePort
  have h1 : ¬ Under a z := fun h' => h (Or.inl h')
  have h2 : ¬ Under b z := fun h' => h (Or.inr h')
  simp only [h1, h2, ↓reduceIte]

open scoped Classical in
/-- Layer of the glued garden. -/
@[expose] noncomputable def glueAt (LN T : LayeredGarden w) (a b aT bT : Fin w × Path)
    (z : Fin w × Path) : ℕ :=
  if InRegion a b z then layerAt T (couplePort a b aT bT z) else layerAt LN z

theorem glueAt_out (LN T : LayeredGarden w) (a b aT bT : Fin w × Path) {z : Fin w × Path}
    (h : ¬ InRegion a b z) : glueAt LN T a b aT bT z = layerAt LN z := by
  unfold glueAt; simp only [h, ↓reduceIte]

theorem glueAt_in (LN T : LayeredGarden w) (a b aT bT : Fin w × Path) {z : Fin w × Path}
    (h : InRegion a b z) : glueAt LN T a b aT bT z = layerAt T (couplePort a b aT bT z) := by
  unfold glueAt; simp only [h, ↓reduceIte]

end WaveTurbulence.Stage1
