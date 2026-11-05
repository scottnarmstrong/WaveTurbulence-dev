/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.WaveB.Molecules
public import WaveTurbulence.Foundations.WaveB.Lemmas
/-! The exact garden molecule is provided by canonical B2 Molecules. Retain its auxiliary tree lemma. -/
public section
namespace WaveTurbulence
open TTree Finset Set
theorem TTree.dropLast_mem_branching {t : TTree} {p : Path} (hp : p ∈ t.nodes) (hne : p ≠ []) :
    p.dropLast ∈ t.branching := by
  have h : p.dropLast ++ [p.getLast hne] = p := List.dropLast_append_getLast hne
  rw [← h] at hp
  exact TTree.branching_of_append_mem t hp

end WaveTurbulence
