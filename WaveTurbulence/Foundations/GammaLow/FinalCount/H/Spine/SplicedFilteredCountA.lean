/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SplicedFilteredCountA
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceFinalCountInputs
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SplicedFilteredBound
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SplicedFilteredCountA`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 Combine the exact frequency-fiber count with countA, retaining the common ladder weight. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Finset
open scoped ENNReal

theorem spliced_filtered_bound_of_countA {w d : ℕ} (G : Garden w) (hp : G.IsPlain)
    (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D) (C : Src.CountingChoices Src.γL G d)
    {L δ C₁ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hC₁ : 0 < C₁)
    (γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (s : Set (GenDecoration G d roots 0)) (hs : s ⊆ splicedSelectedCarrier G D C L γ η base roots) (U V : ℝ≥0∞)
    (hfourier : splicedFourierBoxSum G D.layer D.rootTime
      (splicedFrequencySpectrum G D C.ladderScale L γ η δ base roots) ≤
      U * ENNReal.ofReal (∏ S ∈ G.molecule.maximalLadders,
        Molecule.ladderWeight L γ δ (C.ladderScale S) ^ Molecule.ladderLength S))
    (hcount : G.molecule.countA L γ δ C₁ base
      (Src.splicedCountingAdmissible G D C L γ η base roots) C.ladderScale ≤ V) :
    ‖splicedFilteredKernel G D L γ η δ base roots s‖ₑ ≤
      ‖(coupling d L γ δ : ℂ) ^ G.order‖ₑ * U *
        (V / ENNReal.ofReal (molecularCountNormalization G.molecule d L γ δ C₁)) := by
  have hh := enorm_splicedFilteredKernel_le_count_fourier G hp D hD C hL hδ γ η base roots s hs
  have hfactor := countE_mul_ladderWeight_eq_countA_div G.molecule hL hδ hC₁ γ base
    (Src.splicedCountingAdmissible G D C L γ η base roots) C.ladderScale
  apply hh.trans
  calc
    _ ≤ ‖(coupling d L γ δ : ℂ) ^ G.order‖ₑ *
        ((G.molecule.countE L γ δ base (Src.splicedCountingAdmissible G D C L γ η base roots) : ℝ≥0∞) *
          (U * ENNReal.ofReal (∏ S ∈ G.molecule.maximalLadders,
            Molecule.ladderWeight L γ δ (C.ladderScale S) ^ Molecule.ladderLength S))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfourier (by positivity)) (by positivity)
    _ = ‖(coupling d L γ δ : ℂ) ^ G.order‖ₑ * U *
        (G.molecule.countA L γ δ C₁ base (Src.splicedCountingAdmissible G D C L γ η base roots) C.ladderScale /
          ENNReal.ofReal (molecularCountNormalization G.molecule d L γ δ C₁)) := by
      rw [← hfactor]
      ac_rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left (by rw [div_eq_mul_inv, div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right hcount (by positivity)) (by positivity)

end WaveTurbulence.GammaLow.FinalCount.H
