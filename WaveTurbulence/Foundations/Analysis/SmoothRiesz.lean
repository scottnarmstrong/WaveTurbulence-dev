/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.RieszKernel
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
# Riesz potential bound for smooth functions on convex sets

The segment argument for the Morrey estimate works on closed sets as well
as open ones, so it includes all boundary points of the unit square.
-/

public section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Analysis

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Displacement along a segment is bounded by the integral of the norm of
the Fréchet derivative times the segment length. -/
theorem enorm_sub_le_lintegral_segment {f : Mom d → F} (hf : ContDiff ℝ 1 f)
    (x y : Mom d) :
    ‖f x - f y‖ₑ ≤ ∫⁻ s in Ioc (0 : ℝ) 1,
      ENNReal.ofReal ‖fderiv ℝ f (x + s • (y - x))‖ * ENNReal.ofReal ‖x - y‖ := by
  let path : ℝ → Mom d := fun s => x + s • (y - x)
  have hp : ContDiff ℝ 1 path := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hd (s : ℝ) : HasDerivAt path (y - x) s := by
    convert ((hasDerivAt_id s).smul_const (y - x)).const_add x using 1 <;>
      simp only [path, id_eq, one_smul]
  have hg (s : ℝ) : deriv (f ∘ path) s = fderiv ℝ f (path s) (y - x) :=
    (((hf.differentiable (by norm_num)) (path s)).hasFDerivAt.comp_hasDerivAt s (hd s)).deriv
  have hs := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc
    (hf.comp hp).contDiffOn (by norm_num : (0 : ℝ) ≤ 1)
  have hends : ‖(f ∘ path) 1 - (f ∘ path) 0‖ₑ = ‖f x - f y‖ₑ := by
    simp only [Function.comp_apply, path, one_smul, add_sub_cancel, zero_smul,
      add_zero, enorm_sub_rev]
  rw [hends] at hs
  refine hs.trans ?_
  rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
  apply lintegral_mono
  intro s
  change ‖deriv (f ∘ path) s‖ₑ ≤
    ENNReal.ofReal ‖fderiv ℝ f (path s)‖ * ENNReal.ofReal ‖x - y‖
  rw [hg, ← ENNReal.ofReal_mul (norm_nonneg _), ← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  simpa only [norm_sub_rev] using (fderiv ℝ f (path s)).le_opNorm (y - x)

/-- Riesz-potential estimate on a bounded convex set, before Hölder's
inequality. The assumptions concern the set, the function and the point;
no Sobolev or oscillation estimate is assumed. -/
theorem enorm_mul_volume_le_riesz {f : Mom d → F} (hf : ContDiff ℝ 1 f)
    (hd : 0 < d) {S : Set (Mom d)} (hS : MeasurableSet S) (hconv : Convex ℝ S)
    {x : Mom d} (hx : x ∈ S) {D : ℝ} (hD : 0 < D)
    (hdiam : ∀ y ∈ S, ‖x - y‖ ≤ D) :
    ‖f x‖ₑ * volume S ≤ (∫⁻ y in S, ‖f y‖ₑ) +
      ENNReal.ofReal (D ^ d / d) *
        ∫⁻ z in S, ENNReal.ofReal (‖x - z‖ ^ ((1 : ℝ) - d)) * ‖fderiv ℝ f z‖ₑ := by
  let g : Mom d → ℝ≥0∞ := S.indicator fun z => ‖fderiv ℝ f z‖ₑ
  have hgc : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hgm : Measurable g := hgc.enorm.measurable.indicator hS
  have hseg (y : Mom d) (hy : y ∈ S) :
      ‖f x - f y‖ₑ ≤ ∫⁻ s in Ioc (0 : ℝ) 1,
        g (x + s • (y - x)) * ENNReal.ofReal ‖x - y‖ := by
    have hm (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) : x + s • (y - x) ∈ S := by
      have heq : x + s • (y - x) = (1 - s) • x + s • y := by module
      rw [heq]
      exact hconv hx hy (by linarith [hs.2]) hs.1.le (by ring)
    refine (enorm_sub_le_lintegral_segment hf x y).trans_eq ?_
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro s hs
    dsimp only [g]
    rw [indicator_of_mem (hm s hs), ofReal_norm]
  have hpt (y : Mom d) (hy : y ∈ S) :
      ‖f x‖ₑ ≤ ‖f y‖ₑ + ∫⁻ s in Ioc (0 : ℝ) 1,
        g (x + s • (y - x)) * ENNReal.ofReal ‖x - y‖ := by
    have heq : f y + (f x - f y) = f x := by abel
    have ht := enorm_add_le (f y) (f x - f y)
    rw [heq] at ht
    exact ht.trans (add_le_add le_rfl (hseg y hy))
  calc
    ‖f x‖ₑ * volume S = ∫⁻ _y in S, ‖f x‖ₑ := by rw [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ∫⁻ y in S, ‖f y‖ₑ + ∫⁻ s in Ioc (0 : ℝ) 1,
        g (x + s • (y - x)) * ENNReal.ofReal ‖x - y‖ := setLIntegral_mono' hS hpt
    _ = (∫⁻ y in S, ‖f y‖ₑ) + ∫⁻ y in S, ∫⁻ s in Ioc (0 : ℝ) 1,
        g (x + s • (y - x)) * ENNReal.ofReal ‖x - y‖ :=
      lintegral_add_left hf.continuous.enorm.measurable _
    _ ≤ (∫⁻ y in S, ‖f y‖ₑ) + ENNReal.ofReal (D ^ d / d) *
        ∫⁻ z, ENNReal.ofReal (‖x - z‖ ^ ((1 : ℝ) - d)) * g z :=
      add_le_add le_rfl (lintegral_lintegral_segment_le_riesz hd hgm x hD hS hdiam)
    _ = _ := by
      congr 2
      rw [← lintegral_indicator hS]
      apply lintegral_congr
      intro z
      dsimp only [g]
      by_cases hz : z ∈ S
      · rw [indicator_of_mem hz, indicator_of_mem hz]
      · rw [indicator_of_notMem hz, indicator_of_notMem hz, mul_zero]

end WaveTurbulence.Analysis
