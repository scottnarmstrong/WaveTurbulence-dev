/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.SimpleFunctionInterpolation
public import WaveTurbulence.Foundations.Fourier.SimpleApproximation
public import WaveTurbulence.Foundations.Fourier.FourierL1Pairing
import Mathlib.Tactic

/-!
# Bilinear Hausdorff–Young for integrable `Lᵖ` functions

Simultaneous approximation in `L¹` and `Lᵖ` extends the finite-step
estimate. The continuous `L¹ × L¹` Fourier pairing identifies the limit
with the ordinary Fourier integral, while convergence in `Lᵖ` preserves
the sharp constant one. This proves the bilinear form of TARGET L2370.
-/

public section

open MeasureTheory Filter
open scoped FourierTransform ENNReal Topology

namespace WaveTurbulence.Fourier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- TARGET L2370, bilinear form on `L¹ ∩ Lᵖ`, with constant one. -/
theorem fourier_pairing_Lp {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    {f g : V → ℂ} (hf : Integrable f) (hg : Integrable g)
    (hfp : MemLp f (ENNReal.ofReal p)) (hgp : MemLp g (ENNReal.ofReal p)) :
    ‖∫ ξ, 𝓕 f ξ * g ξ‖ ≤ lpNorm f (ENNReal.ofReal p) volume * lpNorm g (ENNReal.ofReal p) volume := by
  have hpENN : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp1
  let : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p) := ⟨hpENN⟩
  let hf1 := memLp_one_iff_integrable.mpr hf
  let hg1 := memLp_one_iff_integrable.mpr hg
  obtain ⟨F, hF1, hFp, hlimF1, hlimFp⟩ :=
    exists_simpleFunc_L1_Lp_approx ENNReal.ofReal_ne_top hf1 hfp
  obtain ⟨G, hG1, hGp, hlimG1, hlimGp⟩ :=
    exists_simpleFunc_L1_Lp_approx ENNReal.ofReal_ne_top hg1 hgp
  have hFi (n : ℕ) : Integrable (F n) := memLp_one_iff_integrable.mp (hF1 n)
  have hGi (n : ℕ) : Integrable (G n) := memLp_one_iff_integrable.mp (hG1 n)
  have he (n : ℕ) : fourierL1Pairing ((hF1 n).toLp (F n)) ((hG1 n).toLp (G n)) =
      ∫ ξ, 𝓕 (F n : V → ℂ) ξ * G n ξ := fourierL1Pairing_toLp (hFi n) (hGi n)
  have hpair := ((fourierL1Pairing (V := V)).continuous₂.tendsto
    (hf1.toLp f, hg1.toLp g)).comp (hlimF1.prodMk_nhds hlimG1)
  change Tendsto
    (fun n => fourierL1Pairing ((hF1 n).toLp (F n)) ((hG1 n).toLp (G n))) atTop
    (𝓝 (fourierL1Pairing (hf1.toLp f) (hg1.toLp g))) at hpair
  simp_rw [he, fourierL1Pairing_toLp hf hg] at hpair
  have hnormF : Tendsto (fun n => lpNorm (F n) (ENNReal.ofReal p) volume) atTop
      (𝓝 (lpNorm f (ENNReal.ofReal p) volume)) := by
    simpa only [Function.comp_def, Lp.norm_toLp, toReal_eLpNorm] using
      (continuous_norm.tendsto (hfp.toLp f)).comp hlimFp
  have hnormG : Tendsto (fun n => lpNorm (G n) (ENNReal.ofReal p) volume) atTop
      (𝓝 (lpNorm g (ENNReal.ofReal p) volume)) := by
    simpa only [Function.comp_def, Lp.norm_toLp, toReal_eLpNorm] using
      (continuous_norm.tendsto (hgp.toLp g)).comp hlimGp
  exact le_of_tendsto_of_tendsto ((continuous_norm.tendsto _).comp hpair)
    (hnormF.mul hnormG) (Filter.Eventually.of_forall fun n =>
      fourier_pairing_simple hp1 hp2 (F n) (G n) (hFi n) (hGi n))

end WaveTurbulence.Fourier
