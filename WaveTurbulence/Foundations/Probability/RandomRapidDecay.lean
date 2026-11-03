/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Probability.GaussianSummability
public import WaveTurbulence.Foundations.Probability.SchwartzLattice
public import WaveTurbulence.Frozen.Defs.InitialCoeff
public import WaveTurbulence.Foundations.Torus.Series

/-!
# Almost-sure rapid decay and smooth initial data

TARGET (DAT), L290–L293. All natural polynomial weights are summable on one
full-measure event. The coefficients therefore decay rapidly and the torus
Fourier series is smooth. Independence of the Gaussian variables is not needed.
-/

public section

namespace WaveTurbulence.Probability
open MeasureTheory ProbabilityTheory
open scoped ContDiff SchwartzMap

/-- A deterministic rapidly decaying envelope times Gaussian coordinates has
all polynomially weighted absolute sums finite on one full-measure event. -/
theorem ae_summable_all_weights {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {d : ℕ} {c : (Fin d → ℤ) → ℂ} (hc : IsRapidDecay c)
    (g : (Fin d → ℤ) → Ω → ℂ) (hg : ∀ n, HasLaw (g n) stdComplexGaussian P) :
    ∀ᵐ ξ ∂P, ∀ N : ℕ, Summable (fun n => ‖c n * g n ξ‖ * (1 + ‖n‖) ^ N) := by
  apply ae_all_iff.mpr
  intro N
  have h := ae_summable_weighted_gaussian g hg
    (fun n => ‖c n‖ * (1 + ‖n‖) ^ N) (fun n => by positivity)
    (hc.summable_norm_mul_pow N)
  filter_upwards [h] with ξ hξ
  apply hξ.congr
  intro n
  rw [norm_mul]
  ring

/-- Summability of every weighted absolute sum implies rapid decay. -/
theorem isRapidDecay_of_summable_all_weights {d : ℕ} {c : (Fin d → ℤ) → ℂ}
    (hc : ∀ N : ℕ, Summable (fun n => ‖c n‖ * (1 + ‖n‖) ^ N)) : IsRapidDecay c := by
  intro N
  refine ⟨∑' n, ‖c n‖ * (1 + ‖n‖) ^ N, ?_⟩
  intro n
  rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv,
    le_div_iff₀ (pow_pos (by positivity : 0 < 1 + ‖n‖) N)]
  exact (hc N).le_tsum n (fun _ _ => by positivity)

/-- Gaussian multiplication preserves a deterministic rapid-decay envelope almost surely. -/
theorem ae_isRapidDecay_mul_gaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {d : ℕ} {c : (Fin d → ℤ) → ℂ} (hc : IsRapidDecay c)
    (g : (Fin d → ℤ) → Ω → ℂ) (hg : ∀ n, HasLaw (g n) stdComplexGaussian P) :
    ∀ᵐ ξ ∂P, IsRapidDecay (fun n => c n * g n ξ) := by
  filter_upwards [ae_summable_all_weights hc g hg] with ξ hξ
  exact isRapidDecay_of_summable_all_weights hξ

/-- TARGET (DAT): the frozen initial coefficient family is rapidly decaying almost surely. -/
theorem ae_initialCoeff_isRapidDecay {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {d : ℕ} {L : ℝ} (hL : 0 < L) (φ : 𝓢(Mom d, ℝ))
    (g : (Fin d → ℤ) → Ω → ℂ) (hg : ∀ n, HasLaw (g n) stdComplexGaussian P) :
    ∀ᵐ ξ ∂P, IsRapidDecay (initialCoeff L φ g ξ) :=
  ae_isRapidDecay_mul_gaussian (isRapidDecay_sqrt_schwartz hL φ) g hg

/-- TARGET's random initial datum is smooth almost surely. -/
theorem ae_contDiff_initial_torusSeries {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {d : ℕ} {L : ℝ} (hL : 0 < L) (φ : 𝓢(Mom d, ℝ))
    (g : (Fin d → ℤ) → Ω → ℂ) (hg : ∀ n, HasLaw (g n) stdComplexGaussian P) :
    ∀ᵐ ξ ∂P, ContDiff ℝ ∞ (torusSeries L (initialCoeff L φ g ξ)) := by
  filter_upwards [ae_initialCoeff_isRapidDecay hL φ g hg] with ξ hξ
  exact contDiff_torusSeries hL hξ

end WaveTurbulence.Probability
