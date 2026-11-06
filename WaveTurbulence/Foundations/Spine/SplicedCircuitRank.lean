/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceCountingData
public import WaveTurbulence.Foundations.Molecule.MoleculeComponents
/-! The actual source spliced molecule has chi=n-R+1, from its proved incidence counts. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset

theorem spliced_circuitRank {R d : ℕ} (G : Garden (2 * R))
    (C : SourceVine.CountingChoices G d) (h : SourceVine.CountingGeometry G C)
    (hn : 1 ≤ G.order) : G.molecule.circuitRank = (G.order : ℤ) - R + 1 := by
  have hnonempty : G.molecule.atoms.Nonempty := by
    apply Finset.card_pos.mp
    rw [h.atom_count]
    omega
  have hcomp := WaveTurbulence.Mole.numComponents_eq_one G.molecule hnonempty h.connected
  have hE : (G.molecule.bonds.card : ℤ) + R = 2 * (G.order : ℤ) := by
    exact_mod_cast h.bond_count
  unfold Molecule.circuitRank
  rw [h.atom_count, hcomp]
  norm_num only [Nat.cast_one]
  omega

end WaveTurbulence.LGSpine
