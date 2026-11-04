/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.LocalizedVolume

/-!
# Localized hyperplane slices of a complex amplitude

A unit-modulus tangential phase does not affect support, supremum, or normal
Lipschitz bounds. Projection of a ball onto the hyperplane gives a uniform
support set for all normal parameters.
-/

public section

open MeasureTheory Filter Topology Set Metric
open scoped InnerProductSpace NNReal

namespace WaveTurbulence.Resonant

variable {d : ℕ}

/-- A slice with a fixed tangential phase or other bounded tangential multiplier. -/
@[expose] noncomputable def localizedSlice (f : Mom d → ℂ) {ℓ : Mom d}
    (ψ : ↥(ℝ ∙ ℓ)ᗮ → ℂ) (t : ℝ) : ℂ :=
  ∫ w : ↥(ℝ ∙ ℓ)ᗮ, f (t • unitVec ℓ + w) * ψ w

/-- The projection of the support ball fits in one ball independent of the normal parameter. -/
theorem localized_slice_eq_zero_of_notMem
    {f : Mom d → ℂ} {b : Mom d} {R : ℝ} (hR : 0 < R)
    (hs : ∀ y, R < ‖y - b‖ → f y = 0)
    {ℓ : Mom d} (hℓ : ℓ ≠ 0) (t : ℝ) (w : ↥(ℝ ∙ ℓ)ᗮ)
    (hw : w ∉ Metric.ball (-perpPart ℓ (-b)) (2 * R)) :
    f (t • unitVec ℓ + w) = 0 := by
  have hw' : 2 * R ≤ ‖((perpPart ℓ (-b) + w : ↥(ℝ ∙ ℓ)ᗮ) : Mom d)‖ := by
    simpa only [mem_ball, dist_eq_norm, sub_neg_eq_add, add_comm, Submodule.norm_coe, not_lt] using hw
  apply hs
  have hp := norm_perpPart_add_le hℓ (-b) t w
  have he : -b + t • unitVec ℓ + (w : Mom d) = t • unitVec ℓ + w - b := by abel
  rw [he] at hp
  linarith

/-- Compactly supported amplitudes are integrable on the ambient momentum space. -/
theorem integrable_localized_amplitude {f : Mom d → ℂ} {b : Mom d} {R : ℝ}
    (hc : Continuous f) (hs : ∀ y, R < ‖y - b‖ → f y = 0) : Integrable f := by
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (K := Metric.closedBall b R) (isCompact_closedBall b R)
  intro y hy
  by_contra hn
  apply hy
  apply hs
  simpa only [mem_closedBall, dist_eq_norm, not_le] using hn

/-- Supremum bound for a localized slice. -/
theorem norm_localizedSlice_le
    {f : Mom d → ℂ} {b : Mom d} {R D : ℝ} (hR : 0 < R)
    (hs : ∀ y, R < ‖y - b‖ → f y = 0) (hb : ∀ y, ‖f y‖ ≤ D)
    {ℓ : Mom d} (hℓ : ℓ ≠ 0) {ψ : ↥(ℝ ∙ ℓ)ᗮ → ℂ} (hψ : ∀ w, ‖ψ w‖ ≤ 1) (t : ℝ) :
    ‖localizedSlice f ψ t‖ ≤ D * volume.real (Metric.ball (-perpPart ℓ (-b)) (2 * R)) := by
  let S : Set ↥(ℝ ∙ ℓ)ᗮ := Metric.ball (-perpPart ℓ (-b)) (2 * R)
  have hi : Integrable (S.indicator (fun _ => D)) :=
    (integrableOn_const (C := D) (s := S) measure_ball_lt_top.ne).integrable_indicator measurableSet_ball
  rw [localizedSlice]
  refine (norm_integral_le_of_norm_le hi ?_).trans_eq ?_
  · refine Eventually.of_forall fun w => ?_
    by_cases hw : w ∈ S
    · rw [indicator_of_mem hw, norm_mul]
      exact (mul_le_mul_of_nonneg_left (hψ w) (norm_nonneg _)).trans
        (by simpa only [mul_one] using hb (t • unitVec ℓ + w))
    · rw [indicator_of_notMem hw, localized_slice_eq_zero_of_notMem hR hs hℓ t w hw,
        zero_mul, norm_zero]
  · rw [integral_indicator measurableSet_ball]
    simp only [integral_const, smul_eq_mul, measureReal_def, Measure.restrict_apply_univ]
    ring

/-- Every localized slice is integrable on the hyperplane. -/
theorem integrable_localizedSlice_inner
    {f : Mom d → ℂ} {b : Mom d} {R D : ℝ} (hR : 0 < R)
    (hc : Continuous f) (hs : ∀ y, R < ‖y - b‖ → f y = 0) (hb : ∀ y, ‖f y‖ ≤ D)
    {ℓ : Mom d} (hℓ : ℓ ≠ 0) {ψ : ↥(ℝ ∙ ℓ)ᗮ → ℂ}
    (hψc : Continuous ψ) (hψ : ∀ w, ‖ψ w‖ ≤ 1) (t : ℝ) :
    Integrable (fun w : ↥(ℝ ∙ ℓ)ᗮ => f (t • unitVec ℓ + w) * ψ w) := by
  let S : Set ↥(ℝ ∙ ℓ)ᗮ := Metric.ball (-perpPart ℓ (-b)) (2 * R)
  have hi : Integrable (S.indicator (fun _ => D)) :=
    (integrableOn_const (C := D) (s := S) measure_ball_lt_top.ne).integrable_indicator measurableSet_ball
  refine hi.mono' ((hc.comp (continuous_const.add continuous_subtype_val)).mul hψc).aestronglyMeasurable
    (Eventually.of_forall fun w => ?_)
  by_cases hw : w ∈ S
  · rw [indicator_of_mem hw, norm_mul]
    exact (mul_le_mul_of_nonneg_left (hψ w) (norm_nonneg _)).trans
      (by simpa only [mul_one] using hb (t • unitVec ℓ + w))
  · rw [indicator_of_notMem hw, localized_slice_eq_zero_of_notMem hR hs hℓ t w hw,
      zero_mul, norm_zero]

/-- A normal Lipschitz estimate, independent of the tangential phase. -/
theorem lipschitzWith_localizedSlice
    {f : Mom d → ℂ} {b : Mom d} {R D : ℝ} {K : ℝ≥0} (hR : 0 < R)
    (hL : LipschitzWith K f) (hs : ∀ y, R < ‖y - b‖ → f y = 0) (hb : ∀ y, ‖f y‖ ≤ D)
    {ℓ : Mom d} (hℓ : ℓ ≠ 0) {ψ : ↥(ℝ ∙ ℓ)ᗮ → ℂ}
    (hψc : Continuous ψ) (hψ : ∀ w, ‖ψ w‖ ≤ 1) :
    LipschitzWith ⟨(K : ℝ) * volume.real (Metric.ball (-perpPart ℓ (-b)) (2 * R)),
      mul_nonneg K.coe_nonneg ENNReal.toReal_nonneg⟩ (localizedSlice f ψ) := by
  apply LipschitzWith.of_dist_le_mul
  intro t s
  rw [dist_eq_norm]
  change ‖localizedSlice f ψ t - localizedSlice f ψ s‖ ≤
    ((K : ℝ) * volume.real (Metric.ball (-perpPart ℓ (-b)) (2 * R))) * dist t s
  let S : Set ↥(ℝ ∙ ℓ)ᗮ := Metric.ball (-perpPart ℓ (-b)) (2 * R)
  have hi : Integrable (S.indicator (fun _ => (K : ℝ) * dist t s)) :=
    (integrableOn_const (C := (K : ℝ) * dist t s) (s := S)
      measure_ball_lt_top.ne).integrable_indicator measurableSet_ball
  simp only [localizedSlice]
  rw [← integral_sub
    (integrable_localizedSlice_inner hR hL.continuous hs hb hℓ hψc hψ t)
    (integrable_localizedSlice_inner hR hL.continuous hs hb hℓ hψc hψ s)]
  refine (norm_integral_le_of_norm_le hi ?_).trans_eq ?_
  · refine Eventually.of_forall fun w => ?_
    by_cases hw : w ∈ S
    · rw [indicator_of_mem hw, ← sub_mul, norm_mul]
      refine (mul_le_mul_of_nonneg_left (hψ w) (norm_nonneg _)).trans ?_
      rw [mul_one]
      have h := hL.dist_le_mul (t • unitVec ℓ + (w : Mom d)) (s • unitVec ℓ + (w : Mom d))
      rw [dist_eq_norm, dist_add_right, dist_eq_norm, ← sub_smul, norm_smul,
        norm_unitVec hℓ, Real.norm_eq_abs, mul_one, ← Real.dist_eq] at h
      exact h
    · rw [indicator_of_notMem hw,
        localized_slice_eq_zero_of_notMem hR hs hℓ t w hw,
        localized_slice_eq_zero_of_notMem hR hs hℓ s w hw, zero_mul, sub_self, norm_zero]
  · rw [integral_indicator measurableSet_ball]
    simp only [integral_const, smul_eq_mul, measureReal_def, Measure.restrict_apply_univ]
    ring

/-- Integrability of the slice as a function of the normal parameter. -/
theorem integrable_localizedSlice
    {f : Mom d → ℂ} {b : Mom d} {R : ℝ}
    (hc : Continuous f) (hs : ∀ y, R < ‖y - b‖ → f y = 0)
    {ℓ : Mom d} (hℓ : ℓ ≠ 0) {ψ : ↥(ℝ ∙ ℓ)ᗮ → ℂ}
    (hψc : Continuous ψ) (hψ : ∀ w, ‖ψ w‖ ≤ 1) : Integrable (localizedSlice f ψ) := by
  have hbase := (integrable_localized_amplitude hc hs).norm
  have hmp := measurePreserving_sliceEquiv hℓ
  have hn : Integrable ((fun y => ‖f y‖) ∘ sliceEquiv hℓ)
      (volume : Measure (ℝ × ↥(ℝ ∙ ℓ)ᗮ)) :=
    hmp.integrable_comp_emb (sliceEquiv hℓ).measurableEmbedding |>.mpr hbase
  have hm : Continuous (fun p : ℝ × ↥(ℝ ∙ ℓ)ᗮ =>
      f (p.1 • unitVec ℓ + (p.2 : Mom d)) * ψ p.2) :=
    (hc.comp ((continuous_fst.smul continuous_const).add continuous_snd.subtype_val)).mul
      (hψc.comp continuous_snd)
  have hg : Integrable (fun p : ℝ × ↥(ℝ ∙ ℓ)ᗮ =>
      f (p.1 • unitVec ℓ + (p.2 : Mom d)) * ψ p.2) := by
    refine hn.mono' hm.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    simp only [Function.comp_def, sliceEquiv_apply, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hψ p.2)
  change Integrable (fun t : ℝ => ∫ w : ↥(ℝ ∙ ℓ)ᗮ, f (t • unitVec ℓ + w) * ψ w)
  exact hg.integral_prod_left

/-- The `L¹` norm of a slice is bounded by the ambient `L¹` norm. -/
theorem integral_norm_localizedSlice_le_integral
    {f : Mom d → ℂ} {b : Mom d} {R : ℝ}
    (hc : Continuous f) (hs : ∀ y, R < ‖y - b‖ → f y = 0)
    {ℓ : Mom d} (hℓ : ℓ ≠ 0) {ψ : ↥(ℝ ∙ ℓ)ᗮ → ℂ}
    (hψc : Continuous ψ) (hψ : ∀ w, ‖ψ w‖ ≤ 1) :
    (∫ t : ℝ, ‖localizedSlice f ψ t‖) ≤ ∫ y : Mom d, ‖f y‖ := by
  have hbase := (integrable_localized_amplitude hc hs).norm
  have hmp := measurePreserving_sliceEquiv hℓ
  have hn : Integrable ((fun y => ‖f y‖) ∘ sliceEquiv hℓ)
      (volume : Measure (ℝ × ↥(ℝ ∙ ℓ)ᗮ)) :=
    hmp.integrable_comp_emb (sliceEquiv hℓ).measurableEmbedding |>.mpr hbase
  have ht : Integrable (fun t : ℝ => ∫ w : ↥(ℝ ∙ ℓ)ᗮ,
      ‖f (t • unitVec ℓ + w)‖) := by
    simpa only [Function.comp_def, sliceEquiv_apply] using hn.integral_prod_left
  rw [integral_eq_integral_slice hℓ hbase]
  apply integral_mono_ae (integrable_localizedSlice hc hs hℓ hψc hψ).norm ht
  filter_upwards [hn.prod_right_ae] with t ht'
  have hfi : Integrable (fun w : ↥(ℝ ∙ ℓ)ᗮ => ‖f (t • unitVec ℓ + w)‖) := by
    simpa only [Function.comp_def, sliceEquiv_apply] using ht'
  rw [localizedSlice]
  exact norm_integral_le_of_norm_le hfi (Eventually.of_forall fun w => by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hψ w))

/-- Ambient `L¹` bound from localization in a ball. -/
theorem integral_norm_localized_amplitude_le {f : Mom d → ℂ} {b : Mom d} {R D : ℝ}
    (hR : 0 < R) (hc : Continuous f) (hs : ∀ y, R < ‖y - b‖ → f y = 0)
    (hb : ∀ y, ‖f y‖ ≤ D) :
    (∫ y : Mom d, ‖f y‖) ≤ D * volume.real (Metric.ball b (2 * R)) := by
  let S : Set (Mom d) := Metric.ball b (2 * R)
  have hi : Integrable (S.indicator (fun _ => D)) :=
    (integrableOn_const (C := D) (s := S) measure_ball_lt_top.ne).integrable_indicator measurableSet_ball
  refine (integral_mono (integrable_localized_amplitude hc hs).norm hi (fun y => ?_)).trans_eq ?_
  · by_cases hy : y ∈ S
    · rw [indicator_of_mem hy]
      exact hb y
    · rw [indicator_of_notMem hy]
      have hn : 2 * R ≤ ‖y - b‖ := by simpa only [S, mem_ball, dist_eq_norm, not_lt] using hy
      rw [hs y (by linarith), norm_zero]
  · rw [integral_indicator measurableSet_ball]
    simp only [integral_const, smul_eq_mul, measureReal_def, Measure.restrict_apply_univ]
    ring

/-- Uniform ambient-volume bound for the `L¹` norm of every localized slice. -/
theorem integral_norm_localizedSlice_le
    {f : Mom d → ℂ} {b : Mom d} {R D : ℝ} (hR : 0 < R)
    (hc : Continuous f) (hs : ∀ y, R < ‖y - b‖ → f y = 0) (hb : ∀ y, ‖f y‖ ≤ D)
    {ℓ : Mom d} (hℓ : ℓ ≠ 0) {ψ : ↥(ℝ ∙ ℓ)ᗮ → ℂ}
    (hψc : Continuous ψ) (hψ : ∀ w, ‖ψ w‖ ≤ 1) :
    (∫ t : ℝ, ‖localizedSlice f ψ t‖) ≤ D * volume.real (Metric.ball b (2 * R)) :=
  (integral_norm_localizedSlice_le_integral hc hs hℓ hψc hψ).trans
    (integral_norm_localized_amplitude_le hR hc hs hb)

end WaveTurbulence.Resonant
