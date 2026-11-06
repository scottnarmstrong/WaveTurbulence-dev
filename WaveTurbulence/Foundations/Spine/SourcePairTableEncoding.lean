/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourcePairTable
/-! Exact finite encoding of partial incident-dart choices, without a nonempty-dart premise. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open scoped Classical

/-- Every pair of optional choices which is absent together, or incident together,
is represented by the finite source pair table. -/
theorem exists_sourcePairTable {w : ℕ} (G : Garden w)
    (first second : GBranch G.tree → Option (GardenDart G))
    (h : ∀ v, (first v = none ∧ second v = none) ∨
      ∃ x y, first v = some x ∧ second v = some y ∧
        x ∈ G.molecule.dartsAt v ∧ y ∈ G.molecule.dartsAt v) :
    ∃ T : SourcePairTable G, sourcePairFirst G T = first ∧ sourcePairSecond G T = second := by
  classical
  have hex (v : GBranch G.tree) : ∃ p : Option
      ({x : GardenDart G // x ∈ G.molecule.dartsAt v} ×
        {y : GardenDart G // y ∈ G.molecule.dartsAt v}),
      p.map (fun q => q.1.1) = first v ∧ p.map (fun q => q.2.1) = second v := by
    rcases h v with hn | ⟨x, y, hx, hy, hxi, hyi⟩
    · exact ⟨none, by simpa only [Option.map_none] using hn.1.symm,
        by simpa only [Option.map_none] using hn.2.symm⟩
    · exact ⟨some (⟨x, hxi⟩, ⟨y, hyi⟩), hx.symm, hy.symm⟩
  choose T hfirst hsecond using hex
  exact ⟨T, funext hfirst, funext hsecond⟩

end WaveTurbulence.LGSpine
