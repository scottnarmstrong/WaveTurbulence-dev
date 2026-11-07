/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeDegreeCompat

/-! # LayerCnt port shim: the legacy `DegreeBlock` is the universe's `IsBlockDeg` (same body). -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence
namespace Molecule
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

/-- Legacy name of `IsBlockDeg` (degree-only block). -/
abbrev DegreeBlock (S : Finset V) (j₁ j₂ : V) : Prop := M.IsBlockDeg S j₁ j₂

end Molecule
end WaveTurbulence
