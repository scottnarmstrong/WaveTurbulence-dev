/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRestrictInsertion
public import WaveTurbulence.Foundations.Molecule.VineSideLabels
public import WaveTurbulence.Foundations.Molecule.VineSideBonds
import Mathlib.Tactic

/-! # Exact restriction of the type-VII core to its five old side atoms -/

public section
namespace WaveTurbulence.Vine

/-- At old core labels, the side selection keeps exactly the six fixed
side bonds and the two unexpanded cyan rails. -/
theorem typeVII_base_side_bonds (N k : ℕ) (hN : 11 ≤ N) :
    restrictBonds (sideLabels N k) VineType.VII.template.bonds=
      [(4,5),(4,5),(4,6),(4,6),(5,6),(7,8),(5,7),(6,8)] := by
  have h0 : 0 ∉ sideLabels N k := by
    rw [mem_sideLabels_iff]
    omega
  have h1 : 1 ∉ sideLabels N k := by
    rw [mem_sideLabels_iff]
    omega
  have h2 : 2 ∉ sideLabels N k := by
    rw [mem_sideLabels_iff]
    omega
  have h3 : 3 ∉ sideLabels N k := by
    rw [mem_sideLabels_iff]
    omega
  have h4 : 4 ∈ sideLabels N k := by
    rw [mem_sideLabels_iff]
    omega
  have h5 : 5 ∈ sideLabels N k := by
    rw [mem_sideLabels_iff]
    omega
  have h6 : 6 ∈ sideLabels N k := by
    rw [mem_sideLabels_iff]
    omega
  have h7 : 7 ∈ sideLabels N k := by
    rw [mem_sideLabels_iff]
    omega
  have h8 : 8 ∈ sideLabels N k := by
    rw [mem_sideLabels_iff]
    omega
  have h9 : 9 ∉ sideLabels N k := by
    rw [mem_sideLabels_iff]
    omega
  have h10 : 10 ∉ sideLabels N k := by
    rw [mem_sideLabels_iff]
    omega
  simp [restrictBonds,VineType.template,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10]

end WaveTurbulence.Vine
