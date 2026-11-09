/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SplicedFrequencySupport
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceCountingData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceSubproObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SplicedFrequencySupport`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 The actual nonzero spliced summands lie in the ladder input's explicit frequency carrier. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Finset
open scoped ENNReal

theorem sourceLadderGapScales_of_counting {w d : ℕ} {G : Garden w}
    (C : Src.CountingChoices Src.γL G d) (L γ η : ℝ) (base : Mom d)
    (κ : GardenDart G → (Fin d → ℤ)) (h : C.LadderGaps L γ η base κ) :
    sourceLadderGapScales G C.ladderScale L base κ := h

theorem splicedFrequency_mem_spectrum {w d : ℕ} (G : Garden w) (D : SplicedKernelData G d)
    (hD : SplicedAmplitudeBounds G D) (C : Src.CountingChoices Src.γL G d)
    (L γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration G d roots 0)
    (hz : splicedMomentumAmplitude G D L γ η base z.1 ≠ 0)
    (hC : C.Admissible L γ η base (bondIndex G z.1)) :
    splicedFrequency G D L γ δ base z.1 ∈
      splicedFrequencySpectrum G D C.ladderScale L γ η δ base roots := by
  obtain ⟨hε, hZ, hballs⟩ := splicedMomentumAmplitude_support G D hD L γ η base z.1 hz
  rcases hC with ⟨_, _, _, _, _, _, _, _, hgap⟩
  exact ⟨z, hε, hZ, hballs, sourceLadderGapScales_of_counting C L γ η base _ hgap, rfl⟩

end WaveTurbulence.GammaLow.FinalCount.H
