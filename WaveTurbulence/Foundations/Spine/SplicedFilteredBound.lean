/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SplicedSelectedAbsoluteSum
/-! Canonical subpieces preserve the counting bound even when dyadic bins overlap. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set
open scoped ENNReal

noncomputable def splicedFilteredKernel {w d : ℕ} (G : Garden w) (D : SplicedKernelData G d)
    (L γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (s : Set (GenDecoration G d roots 0)) : ℂ :=
  (coupling d L γ δ : ℂ) ^ G.order *
    ∑' z : s, splicedMomentumAmplitude G D L γ η base z.1.1 *
      splicedFourierB G D.layer D.rootTime (splicedFrequency G D L γ δ base z.1.1)

/-- A canonical selection may refine overlapping dyadic bins. The absolute-frequency
estimate applies to any such subpiece; no cancellation is presumed monotone. -/
theorem enorm_splicedFilteredKernel_le_count_fourier {w d : ℕ} (G : Garden w) (hp : G.IsPlain)
    (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D) (C : SourceVine.CountingChoices G d)
    {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (γ η : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (s : Set (GenDecoration G d roots 0))
    (hs : s ⊆ splicedSelectedCarrier G D C L γ η base roots) :
    ‖splicedFilteredKernel G D L γ η δ base roots s‖ₑ ≤
      ‖(coupling d L γ δ : ℂ) ^ G.order‖ₑ *
        ((G.molecule.countE L γ δ base (splicedCountingAdmissible G D C L γ η base roots) : ℝ≥0∞) *
          splicedFourierBoxSum G D.layer D.rootTime
            (splicedFrequencySpectrum G D C.ladderScale L γ η δ base roots)) := by
  unfold splicedFilteredKernel
  rw [enorm_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply enorm_tsum_le_tsum_enorm |>.trans
  apply (ENNReal.tsum_mono_subtype
    (fun z : GenDecoration G d roots 0 => ‖splicedMomentumAmplitude G D L γ η base z.1 *
      splicedFourierB G D.layer D.rootTime (splicedFrequency G D L γ δ base z.1)‖ₑ) hs).trans
  exact tsum_enorm_splicedSelectedSummands_le_count_fourier G hp D hD C hL hδ γ η base roots

end WaveTurbulence.LGSpine
