/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.Spine.SourceCountingData
public import WaveTurbulence.Foundations.Molecule.MoleculeComponents
/-! The actual source spliced molecule has chi=n-R+1, from its proved incidence counts. -/
public section
set_option autoImplicit false
-- Ported from main `Spine.SplicedCircuitRank` (sha256 cfb34a93f66e81f5fcfb76ce6486e0e91a4d57980ca3a31f2dc5bdd9e0e85e6d) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}
open Finset

theorem spliced_circuitRank {R d : ℕ} (G : Garden (2 * R))
    (C : CountingChoices γv G d) (h : CountingGeometry G C)
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

end WaveTurbulence.GammaLow.Famc
