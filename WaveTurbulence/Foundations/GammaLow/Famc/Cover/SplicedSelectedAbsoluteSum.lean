/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedFrequencyCount
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedFrequencySupport
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedSelectedKernel
public import WaveTurbulence.Foundations.Spine.SplicedSelectedKernel
public import Mathlib.Analysis.Normed.Group.InfiniteSum
/-! Absolute-summand form of TARGET redvine5, allowing canonical disjoint subpieces. -/
public section
set_option autoImplicit false
-- Ported from main `Spine.SplicedSelectedAbsoluteSum` (sha256 605df2a553be32407a669de83ef582384b23db16243cb8cdb388756676dbc324) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}
open WaveTurbulence.Induct
open Set
open scoped ENNReal

theorem tsum_enorm_splicedSelectedSummands_le_count_fourier {w d : ℕ} (G : Garden w) (hp : G.IsPlain)
    (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D) (C : CountingChoices γv G d)
    {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (γ η : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) :
    (∑' z : splicedSelectedCarrier G D C L γ η base roots,
      ‖splicedMomentumAmplitude G D L γ η base z.1.1 *
        splicedFourierB G D.layer D.rootTime (splicedFrequency G D L γ δ base z.1.1)‖ₑ) ≤
        ((G.molecule.countE L γ δ base (FinalCount.Src.splicedCountingAdmissible G D C L γ η base roots) : ℝ≥0∞) *
          splicedFourierBoxSum G D.layer D.rootTime
            (splicedFrequencySpectrum G D C.ladderScale L γ η δ base roots)) := by
  let A := splicedFrequencySpectrum G D C.ladderScale L γ η δ base roots
  let π := splicedSelectedBox G D hD C L γ η δ base roots
  let B : sourceFrequencyBoxes G A → ℝ≥0∞ := fun σ =>
    ⨆ (α : GBranch G.tree → ℝ) (_ : α ∈ A) (_ : ∀ v, |α v - σ.1 v| ≤ 1),
      ‖splicedFourierB G D.layer D.rootTime α‖ₑ
  have hh := tsum_le_fiber_count_mul π
    (fun z => ‖splicedMomentumAmplitude G D L γ η base z.1.1 *
      splicedFourierB G D.layer D.rootTime (splicedFrequency G D L γ δ base z.1.1)‖ₑ)
    B (G.molecule.countE L γ δ base (FinalCount.Src.splicedCountingAdmissible G D C L γ η base roots))
    (splicedSelectedBox_fiber_count G hp D hD C hL hδ γ η base roots) (by
      intro z
      have hα := splicedFrequency_mem_spectrum G D hD C L γ η δ base roots z.1 z.2.1 z.2.2
      have hB := enorm_splicedFourierB_le_box G D.layer D.rootTime A
        (splicedFrequency G D L γ δ base z.1.1) hα
      have hAmp : ‖splicedMomentumAmplitude G D L γ η base z.1.1‖ₑ ≤ 1 := by
        rw [← ofReal_norm]
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
          (norm_splicedMomentumAmplitude_le_one G D hD L γ η base z.1.1)
      rw [enorm_mul]
      apply (mul_le_mul_of_nonneg_right hAmp (by positivity)).trans
      simpa only [one_mul, B, π, splicedSelectedBox] using hB)
  exact hh

end WaveTurbulence.GammaLow.Famc
