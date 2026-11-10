/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LatticeBracketBounds
public import WaveTurbulence.Foundations.Canon.Basic
/-! The corrected root-to-leaf weight transfer on the exact decorated forest carrier. -/
public section
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

/-- Each node has a nonempty set of descendant leaves, including the trivial-tree case. -/
theorem leavesBelow_nonempty {w : ℕ} {tree : Fin w → TTree} (a : GNode tree) :
    a.leavesBelow.Nonempty := by
  obtain ⟨m, hm⟩ := Canon.odd_card_leavesBelow a
  apply Finset.card_pos.mp
  omega

end WaveTurbulence.LGSpine
