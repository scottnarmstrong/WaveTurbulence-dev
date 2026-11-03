/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.SmoothArcEnvelope
public import WaveTurbulence.Foundations.WeylSums.ArcIntegration

/-!
# Unit-interval moments of smooth quadratic sums

Integrating the rational-arc majorant leaves a harmonic denominator sum at
power four and a convergent denominator sum at every higher real power.
The estimates are uniform in the integer center and real linear frequency.
-/

public section

open MeasureTheory Finset
open scoped BigOperators ContDiff

namespace WaveTurbulence.WeylSums

/-- Integrated major-arc bound, before estimating the denominator sum.
The same cutoff-dependent constant works for every real exponent `p>2`. -/
theorem exists_smooth_unit_moment_bound (χ : ℝ → ℂ)
    (hc : HasCompactSupport χ) (hs : ContDiff ℝ ∞ χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (p r : ℝ) (h : ℤ), 2 < p →
      IntegrableOn (fun t : ℝ => ‖smoothGaussSum χ N t r h‖ ^ p) (Set.Ioc (0 : ℝ) 1) ∧
      (∫ t : ℝ in 0..1, ‖smoothGaussSum χ N t r h‖ ^ p) ≤
        (C * N) ^ p * (4 * arcProfileMass (p / 2) / (N : ℝ) ^ 2 * arcDenominatorSum (p / 2) N) := by
  obtain ⟨C, hC, hpoint⟩ := exists_smooth_rationalArcEnvelope_bound χ hc hs
  refine ⟨C, hC, ?_⟩
  intro N hN p r h hp
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hN)
  have hσ : 1 < p / 2 := by linarith only [hp]
  have hp0 : 0 ≤ p := by linarith only [hp]
  let f : ℝ → ℝ := fun t => ‖smoothGaussSum χ N t r h‖ ^ p
  let g : ℝ → ℝ := fun t => (C * N) ^ p * rationalArcEnvelope N (p / 2) N t
  have hg : Integrable g := (integrable_rationalArcEnvelope hNpos hσ N).const_mul _
  have hg0 (t : ℝ) : 0 ≤ g t := mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (rationalArcEnvelope_nonneg _ _ _ _)
  have hle : f ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hpoint N hN p t r h hp0 ⟨ht.1.le, ht.2⟩
  have hfm : AEStronglyMeasurable f (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    ((measurable_smoothGaussSum χ N r h).norm.pow_const p).aestronglyMeasurable
  have hf : Integrable f (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    apply hg.restrict.mono' hfm
    filter_upwards [hle] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact ht
  refine ⟨hf, ?_⟩
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  calc
    _ ≤ ∫ t in Set.Ioc (0 : ℝ) 1, g t := integral_mono_ae hf hg.restrict hle
    _ ≤ ∫ t : ℝ, g t := setIntegral_le_integral hg (Filter.Eventually.of_forall hg0)
    _ = (C * N) ^ p * ∫ t : ℝ, rationalArcEnvelope N (p / 2) N t := integral_const_mul _ _
    _ ≤ (C * N) ^ p * (4 * (arcProfileMass (p / 2) / (N : ℝ) ^ 2) * arcDenominatorSum (p / 2) N) :=
      mul_le_mul_of_nonneg_left (integral_rationalArcEnvelope_le hNpos hσ N)
        (Real.rpow_nonneg (by positivity) _)
    _ = _ := by ring

end WaveTurbulence.WeylSums
