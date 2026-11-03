/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.WeylSupremumArcs
public import WaveTurbulence.Foundations.WeylSums.ArcIntegration

/-! # Global moments of the supremum Weyl sum -/

public section
open MeasureTheory
namespace WaveTurbulence.WeylSums

/-- Global major-arc integration, retaining the explicit convergent series. -/
theorem exists_weylSupremum_integral_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (L p : ℝ), 1 ≤ L → 4 < p →
      IntegrableOn (fun t : ℝ => weylSupremum L t ^ p) (Set.Ioc (0 : ℝ) 1) ∧
      (∫ t : ℝ in 0..1, weylSupremum L t ^ p) ≤
        (C * L) ^ p * (4 * arcProfileMass (p / 2) / L ^ 2 *
          ∑' q : ℕ, (q : ℝ) ^ (1 - p / 2)) := by
  obtain ⟨C, hC, hpoint⟩ := exists_weylSupremum_arc_bound
  refine ⟨C, hC, ?_⟩
  intro L p hL hp
  have hLpos : 0 < L := by linarith
  have hσ : 1 < p / 2 := by linarith
  let f : ℝ → ℝ := fun t => weylSupremum L t ^ p
  let g : ℝ → ℝ := fun t => (C * L) ^ p * rationalArcEnvelope L (p / 2) ⌊L⌋₊ t
  have hg : Integrable g := (integrable_rationalArcEnvelope hLpos hσ ⌊L⌋₊).const_mul _
  have hg0 (t : ℝ) : 0 ≤ g t := mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (rationalArcEnvelope_nonneg _ _ _ _)
  have hle : f ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hpoint L p t hL (by linarith) ⟨ht.1.le, ht.2⟩
  have hfm : AEStronglyMeasurable f (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    ((measurable_weylSupremum hLpos).pow_const p).aestronglyMeasurable
  have hf : Integrable f (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    apply hg.restrict.mono' hfm
    filter_upwards [hle] with t ht
    change ‖weylSupremum L t ^ p‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (weylSupremum_nonneg hLpos t) _)]
    exact ht
  refine ⟨hf, ?_⟩
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  calc
    _ ≤ ∫ t in Set.Ioc (0 : ℝ) 1, g t := integral_mono_ae hf hg.restrict hle
    _ ≤ ∫ t : ℝ, g t := setIntegral_le_integral hg (Filter.Eventually.of_forall hg0)
    _ = (C * L) ^ p * ∫ t : ℝ, rationalArcEnvelope L (p / 2) ⌊L⌋₊ t := integral_const_mul _ _
    _ ≤ (C * L) ^ p * (4 * (arcProfileMass (p / 2) / L ^ 2) * arcDenominatorSum (p / 2) ⌊L⌋₊) :=
      mul_le_mul_of_nonneg_left (integral_rationalArcEnvelope_le hLpos hσ ⌊L⌋₊)
        (Real.rpow_nonneg (by positivity) _)
    _ ≤ _ := by
      rw [show 4 * (arcProfileMass (p / 2) / L ^ 2) = 4 * arcProfileMass (p / 2) / L ^ 2 by ring]
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
      exact mul_le_mul_of_nonneg_left (arcDenominatorSum_le_tsum (by linarith) ⌊L⌋₊)
        (by have := arcProfileMass_nonneg (p / 2); positivity)

end WaveTurbulence.WeylSums
