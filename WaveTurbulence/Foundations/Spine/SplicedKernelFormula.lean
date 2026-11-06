/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SplicedFiniteSupport
public import WaveTurbulence.Foundations.Spine.SplicedSumIntegral
/-! Exact original-kernel formula and fixed-choice specialization, preserving the source support. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
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
    (D : SplicedKernelData G d) (C : SourceVine.CountingChoices G d)
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

end WaveTurbulence.LGSpine
