/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.Molecules

/-! # Atom-and-dart isomorphisms of actual directed molecules -/

public section
namespace WaveTurbulence.Mole

/-- Both atom and half-edge bijections, with all defining structure preserved. -/
structure DirectedMoleculeIso {V D W E : Type*} (M : Molecule V D) (N : Molecule W E) where
  atoms : M.atoms ≃ N.atoms
  darts : D ≃ E
  atom_comm : ∀ x, N.atom (darts x) = (atoms ⟨M.atom x,M.atom_mem x⟩).1
  mate_comm : ∀ x, N.mate (darts x) = darts (M.mate x)
  out_comm : ∀ x, N.out (darts x) = M.out x

end WaveTurbulence.Mole
