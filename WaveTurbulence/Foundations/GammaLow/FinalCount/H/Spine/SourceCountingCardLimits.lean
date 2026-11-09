/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceCountingCardLimits
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceCountingData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceCountingCardLimits`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 Elementary cardinal bounds for the actual source counting data. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open Finset

theorem numCriticalSG_le_order {w d : ℕ} (G : Garden w) (C : Src.CountingChoices Src.γL G d) :
    C.numCriticalSG ≤ G.order := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (by simp only [card_univ, card_gbranch]; rfl)

theorem source_scale_count_le_rho_add_critical {w d : ℕ} (G : Garden w)
    (C : Src.CountingChoices Src.γL G d) :
    G.molecule.maximalLadders.card + C.numCriticalSG ≤ G.molecule.rho + C.numCriticalSG :=
  Nat.add_le_add_right (source_numLadders_le_rho G) _

end WaveTurbulence.GammaLow.FinalCount.H
