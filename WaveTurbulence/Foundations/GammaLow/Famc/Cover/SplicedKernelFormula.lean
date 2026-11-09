/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedFiniteSupport
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedFrequencyCount
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedFrequencySupport
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedSelectedKernel
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedSumIntegral
public import WaveTurbulence.Foundations.Spine.SplicedFiniteSupport
public import WaveTurbulence.Foundations.Spine.SplicedSumIntegral
/-! Exact original-kernel formula and fixed-choice specialization, preserving the source support. -/
public section
set_option autoImplicit false
-- Ported from main `Spine.SplicedKernelFormula` (sha256 0f057f687b2628c533c7ce25307c156c8b1a9c9f08dfd3de972113e64dfbff51) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}
open WaveTurbulence.Induct
open Set

 theorem splicedKernel_eq_amplitude_fourier {w d : ℕ} (G : Garden w) (D : SplicedKernelData G d)
    (L γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) :
    splicedKernel G D L γ η δ base roots =
      (coupling d L γ δ : ℂ) ^ G.order * ∑' z : GenDecoration G d roots 0,
        splicedMomentumAmplitude G D L γ η base z.1 *
          splicedFourierB G D.layer D.rootTime (splicedFrequency G D L γ δ base z.1) := by
  unfold splicedKernel splicedMomentumAmplitude
  congr 1
  apply tsum_congr
  intro z
  rw [splicedTimeIntegral_eq_fourierB]

 theorem splicedSelectedKernel_eq_splicedKernel_of_support {w d : ℕ} (G : Garden w)
    (D : SplicedKernelData G d) (C : CountingChoices γv G d)
    (L γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (hC : ∀ z : GenDecoration G d roots 0, splicedMomentumAmplitude G D L γ η base z.1 ≠ 0 →
      C.Admissible L γ η base (bondIndex G z.1)) :
    splicedSelectedKernel G D C L γ η δ base roots = splicedKernel G D L γ η δ base roots := by
  rw [splicedKernel_eq_amplitude_fourier]
  unfold splicedSelectedKernel
  congr 1
  exact tsum_subtype_eq_of_support_subset (f := fun z : GenDecoration G d roots 0 =>
    splicedMomentumAmplitude G D L γ η base z.1 *
      splicedFourierB G D.layer D.rootTime (splicedFrequency G D L γ δ base z.1)) (s := splicedSelectedCarrier G D C L γ η base roots) (by
    intro z hz
    have hn : splicedMomentumAmplitude G D L γ η base z.1 ≠ 0 := by
      intro he
      exact hz (by dsimp only; rw [he, zero_mul])
    exact ⟨hn, hC z hn⟩)

end WaveTurbulence.GammaLow.Famc
