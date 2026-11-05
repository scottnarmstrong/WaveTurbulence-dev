/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineInteriorConnected
import Mathlib.Tactic

/-! # Full-degree selection propagates through a connected nonjoint region -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Once one interior atom is selected, full-degree closure selects the
entire connected interior, and selected joints complete the atomic group. -/
theorem full_interior_selection (M : Molecule V D) (hM : M.IsMolecule)
    {A S : Finset V} {a b u : V} (hA : A ⊆ M.atoms) (ha : a ∈ A) (hb : b ∈ A)
    (hC : GroupConnected M (S \ {a,b}))
    (hfull : ∀ v ∈ A,v ∈ S \ {a,b} → M.degIn A v=4)
    (huA : u ∈ A) (huI : u ∈ S \ {a,b}) : S ⊆ A := by
  intro v hv
  by_cases hvj : v ∈ ({a,b} : Finset V)
  · rcases mem_insert.mp hvj with hva | hvb
    · exact hva.symm ▸ ha
    · exact (mem_singleton.mp hvb).symm ▸ hb
  · have hp := hC u huI v (mem_sdiff.mpr ⟨hv,hvj⟩)
    exact (Mole.induced_path_barrier M hM hA hfull hp).mp huA

end WaveTurbulence.Vine
