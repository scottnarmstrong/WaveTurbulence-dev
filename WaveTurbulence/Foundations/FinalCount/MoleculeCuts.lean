/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeBasic
import Mathlib.Tactic

/-!
# Exact half-edge cut identities

TARGET Definition `defcut` L2117–L2127 and F40: the chosen incoming and
outgoing darts stay at the original atom, and all its other darts move to
the fresh atom. This includes degree-two cuts and self-loops.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) {v v2 : V} {x1 x2 : D}

omit [DecidableEq V] [Fintype D] [DecidableEq D] in
theorem cut_fresh_ne (hd : M.IsCutData v v2 x1 x2) : v2 ≠ v := by
  intro he
  exact hd.2.1 (he.symm ▸ hd.1)

end WaveTurbulence.Mole
