/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedFilteredBound
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedFrequencyCount
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedFrequencySupport
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedSelectedAbsoluteSum
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedSelectedKernel
public import WaveTurbulence.Foundations.Spine.SplicedFilteredBound
public import WaveTurbulence.Foundations.Spine.CountANormalization
/-! Combine the exact frequency-fiber count with countA, retaining the common ladder weight. -/
public section
set_option autoImplicit false
-- Ported from main `Spine.SplicedFilteredCountA` (sha256 bc40e3f03a079ce3b724c88d64876ef253c050e419c22967c6039c46346a0e2e) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}
open WaveTurbulence.Induct
open Set Finset
open scoped ENNReal

theorem spliced_filtered_bound_of_countA {w d : ℕ} (G : Garden w) (hp : G.IsPlain)
    (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D) (C : CountingChoices γv G d)
    {L δ C₁ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hC₁ : 0 < C₁)
    (γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (s : Set (GenDecoration G d roots 0)) (hs : s ⊆ splicedSelectedCarrier G D C L γ η base roots) (U V : ℝ≥0∞)
    (hfourier : splicedFourierBoxSum G D.layer D.rootTime
      (splicedFrequencySpectrum G D C.ladderScale L γ η δ base roots) ≤
      U * ENNReal.ofReal (∏ S ∈ G.molecule.maximalLadders,
        Molecule.ladderWeight L γ δ (C.ladderScale S) ^ Molecule.ladderLength S))
    (hcount : G.molecule.countA L γ δ C₁ base
      (FinalCount.Src.splicedCountingAdmissible G D C L γ η base roots) C.ladderScale ≤ V) :
    ‖splicedFilteredKernel G D L γ η δ base roots s‖ₑ ≤
      ‖(coupling d L γ δ : ℂ) ^ G.order‖ₑ * U *
        (V / ENNReal.ofReal (molecularCountNormalization G.molecule d L γ δ C₁)) := by
  have hh := enorm_splicedFilteredKernel_le_count_fourier G hp D hD C hL hδ γ η base roots s hs
  have hfactor := countE_mul_ladderWeight_eq_countA_div G.molecule hL hδ hC₁ γ base
    (FinalCount.Src.splicedCountingAdmissible G D C L γ η base roots) C.ladderScale
  apply hh.trans
  calc
    _ ≤ ‖(coupling d L γ δ : ℂ) ^ G.order‖ₑ *
        ((G.molecule.countE L γ δ base (FinalCount.Src.splicedCountingAdmissible G D C L γ η base roots) : ℝ≥0∞) *
          (U * ENNReal.ofReal (∏ S ∈ G.molecule.maximalLadders,
            Molecule.ladderWeight L γ δ (C.ladderScale S) ^ Molecule.ladderLength S))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfourier (by positivity)) (by positivity)
    _ = ‖(coupling d L γ δ : ℂ) ^ G.order‖ₑ * U *
        (G.molecule.countA L γ δ C₁ base (FinalCount.Src.splicedCountingAdmissible G D C L γ η base roots) C.ladderScale /
          ENNReal.ofReal (molecularCountNormalization G.molecule d L γ δ C₁)) := by
      rw [← hfactor]
      ac_rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left (by rw [div_eq_mul_inv, div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right hcount (by positivity)) (by positivity)

end WaveTurbulence.GammaLow.Famc
