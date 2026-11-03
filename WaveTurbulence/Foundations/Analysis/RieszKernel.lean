/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Frozen.Defs.Mom
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Segment integration and the Riesz kernel

The kernel collapse used to prove Morrey estimates. These lemmas integrate
along segments from a point to a measurable set of bounded diameter.
Adapted from the smooth convex-domain arguments in Scott's elliptic regularity
library, using the campaign's Euclidean momentum carrier.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Analysis

variable {d : ℕ}

/-- The elementary parameter integral behind the kernel collapse. -/
theorem lintegral_segment_parameter_le {D r : ℝ} (hd : 0 < d) (hD : 0 < D) (hr : 0 < r) :
    ∫⁻ s in Ioc (0 : ℝ) 1,
        ENNReal.ofReal (s⁻¹ * (s ^ d)⁻¹) * (if r ≤ s * D then 1 else 0) ≤
      ENNReal.ofReal (D ^ d / (d * r ^ d)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set a : ℝ := r / D with ha
  have ha0 : 0 < a := div_pos hr hD
  have hstep : ∫⁻ s in Ioc (0 : ℝ) 1,
        ENNReal.ofReal (s⁻¹ * (s ^ d)⁻¹) * (if r ≤ s * D then 1 else 0) ≤
      ∫⁻ s in Ioi a, ENNReal.ofReal (s ^ (-((d : ℝ) + 1))) := by
    calc _ ≤ ∫⁻ s in Ioc (0 : ℝ) 1,
            (Ici a).indicator (fun s => ENNReal.ofReal (s ^ (-((d : ℝ) + 1)))) s := by
          refine setLIntegral_mono (Measurable.indicator (by fun_prop) measurableSet_Ici) ?_
          intro s hs
          by_cases hsa : r ≤ s * D
          · have hsa' : a ≤ s := by
              rw [ha, div_le_iff₀ hD]; exact hsa
            simp only [indicator_of_mem (mem_Ici.2 hsa'), hsa, ↓reduceIte, mul_one]
            refine le_of_eq (by
              congr 1
              rw [Real.rpow_neg hs.1.le, Real.rpow_add hs.1, Real.rpow_natCast, Real.rpow_one]
              field_simp)
          · simp [hsa]
      _ ≤ ∫⁻ s, (Ici a).indicator (fun s => ENNReal.ofReal (s ^ (-((d : ℝ) + 1)))) s :=
          setLIntegral_le_lintegral _ _
      _ = ∫⁻ s in Ici a, ENNReal.ofReal (s ^ (-((d : ℝ) + 1))) :=
          lintegral_indicator measurableSet_Ici _
      _ = _ := setLIntegral_congr Ioi_ae_eq_Ici.symm
  refine hstep.trans ?_
  have hint : IntegrableOn (fun s : ℝ => s ^ (-((d : ℝ) + 1))) (Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) ha0
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi a)] fun s : ℝ => s ^ (-((d : ℝ) + 1)) :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs =>
      Real.rpow_nonneg (ha0.trans hs).le _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn,
    integral_Ioi_rpow_of_lt (by linarith) ha0]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  have : -((d : ℝ) + 1) + 1 = -(d : ℝ) := by ring
  rw [this, Real.rpow_neg ha0.le, Real.rpow_natCast, ha, div_pow]
  field_simp

/-- Dilation about `x` by a positive factor `s` scales the Lebesgue lintegral by `(s ^ d)⁻¹`. -/
theorem lintegral_comp_dilation {H : Mom d → ℝ≥0∞} (hH : Measurable H) (x : Mom d) {s : ℝ}
    (hs : 0 < s) :
    ∫⁻ y, H (x + s • (y - x)) = ENNReal.ofReal ((s ^ d)⁻¹) * ∫⁻ z, H z := by
  have h1 : ∫⁻ y, H (x + s • (y - x)) = ∫⁻ w, H (x + s • w) :=
    lintegral_sub_right_eq_self (fun w => H (x + s • w)) x
  have h2 : ∫⁻ w, H (x + s • w) = ∫⁻ w, (fun z => H (x + z)) (s • w) := rfl
  have hmap := Measure.map_addHaar_smul (volume : Measure (Mom d)) hs.ne'
  have hfin : Module.finrank ℝ (Mom d) = d := by simp
  rw [h1, h2, ← lintegral_map (f := fun z => H (x + z)) (by fun_prop)
    (measurable_const_smul s), hmap, hfin, abs_of_pos (by positivity), lintegral_smul_measure,
    lintegral_add_left_eq_self (fun z => H z) x, smul_eq_mul]

private theorem norm_sub_dilation_of_pos (x y : Mom d) {s : ℝ} (hs : 0 < s) :
    norm (x - (x + s • (y - x))) = s * norm (x - y) := by
  have : x - (x + s • (y - x)) = s • (x - y) := by
    module
  rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hs]

/-- The weight along the segments at parameter `s`, truncated to `|x - z| ≤ s D`. -/
@[expose] noncomputable def segmentSliceWeight (g : Mom d → ℝ≥0∞) (x : Mom d) (D s : ℝ) (z : Mom d) :
    ℝ≥0∞ :=
  if norm (x - z) ≤ s * D then
    ENNReal.ofReal (norm (x - z)) * g z else 0

theorem measurable_segmentSliceWeight {g : Mom d → ℝ≥0∞} (hg : Measurable g) (x : Mom d)
    (D s : ℝ) : Measurable (segmentSliceWeight g x D s) := by
  unfold segmentSliceWeight
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_le (continuous_norm.comp
      (continuous_const.sub continuous_id)).measurable measurable_const
  · exact (ENNReal.measurable_ofReal.comp (continuous_norm.comp
      (continuous_const.sub continuous_id)).measurable).mul hg

/-- The change of variables for one segment parameter. -/
theorem lintegral_segment_slice_le {g : Mom d → ℝ≥0∞} (hg : Measurable g) (x : Mom d) {D : ℝ}
    {S : Set (Mom d)} (hS : MeasurableSet S) (hSD : ∀ y ∈ S, norm (x - y) ≤ D)
    {s : ℝ} (hs : 0 < s) :
    ∫⁻ y in S, g (x + s • (y - x)) * ENNReal.ofReal (norm (x - y)) ≤
      ENNReal.ofReal (s⁻¹ * (s ^ d)⁻¹) * ∫⁻ z, segmentSliceWeight g x D s z := by
  have hpt : ∀ y ∈ S, g (x + s • (y - x)) * ENNReal.ofReal (norm (x - y)) =
      ENNReal.ofReal s⁻¹ * segmentSliceWeight g x D s (x + s • (y - x)) := by
    intro y hy
    have hn := norm_sub_dilation_of_pos x y hs
    have hle : norm (x - (x + s • (y - x))) ≤ s * D := by
      rw [hn]; exact mul_le_mul_of_nonneg_left (hSD y hy) hs.le
    simp only [segmentSliceWeight, hle, ↓reduceIte]
    rw [hn]
    rw [ENNReal.ofReal_mul hs.le, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      inv_mul_cancel₀ hs.ne', ENNReal.ofReal_one, one_mul, mul_comm]
  calc ∫⁻ y in S, g (x + s • (y - x)) * ENNReal.ofReal (norm (x - y))
      = ∫⁻ y in S, ENNReal.ofReal s⁻¹ * segmentSliceWeight g x D s (x + s • (y - x)) :=
        setLIntegral_congr_fun hS hpt
    _ ≤ ∫⁻ y, ENNReal.ofReal s⁻¹ * segmentSliceWeight g x D s (x + s • (y - x)) :=
        setLIntegral_le_lintegral _ _
    _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_comp_dilation
          (measurable_segmentSliceWeight hg x D s) x hs, ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity)]

private theorem lintegral_time_collapse_pointwise (hd : 0 < d) {g : Mom d → ℝ≥0∞} {D : ℝ}
    (hD : 0 < D) (x z : Mom d) :
    ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (s⁻¹ * (s ^ d)⁻¹) *
        segmentSliceWeight g x D s z ≤
      ENNReal.ofReal (D ^ d / d) *
        (ENNReal.ofReal (norm (x - z) ^ ((1 : ℝ) - d)) * g z) := by
  set r := norm (x - z) with hr
  have hrnn : 0 ≤ r := norm_nonneg _
  rcases hrnn.eq_or_lt with hr0 | hrpos
  · have : ∀ s : ℝ, segmentSliceWeight g x D s z = 0 := by
      intro s; unfold segmentSliceWeight; rw [← hr, ← hr0]; simp
    simp [this]
  · have hW : ∀ s : ℝ, segmentSliceWeight g x D s z =
        (ENNReal.ofReal r * g z) * (if r ≤ s * D then 1 else 0) := by
      intro s; unfold segmentSliceWeight; rw [← hr]; split_ifs <;> simp
    have hcol := lintegral_segment_parameter_le (r := r) hd hD hrpos
    calc _ = ∫⁻ s in Ioc (0 : ℝ) 1, (ENNReal.ofReal r * g z) *
            (ENNReal.ofReal (s⁻¹ * (s ^ d)⁻¹) * (if r ≤ s * D then 1 else 0)) := by
          refine lintegral_congr fun s => ?_
          rw [hW]; ring
      _ = (ENNReal.ofReal r * g z) * ∫⁻ s in Ioc (0 : ℝ) 1,
            ENNReal.ofReal (s⁻¹ * (s ^ d)⁻¹) * (if r ≤ s * D then 1 else 0) := by
          rw [lintegral_const_mul]
          refine ENNReal.measurable_ofReal.comp (by fun_prop) |>.mul ?_
          exact Measurable.ite (measurableSet_le measurable_const (by fun_prop)) measurable_const
            measurable_const
      _ ≤ (ENNReal.ofReal r * g z) * ENNReal.ofReal (D ^ d / (d * r ^ d)) :=
          by gcongr
      _ = _ := by
          have hid : r * (D ^ d / (d * r ^ d)) = D ^ d / d * r ^ ((1 : ℝ) - d) := by
            rw [Real.rpow_sub hrpos, Real.rpow_one, Real.rpow_natCast]
            have : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
            have : r ^ d ≠ 0 := by positivity
            field_simp
          have hid' : ENNReal.ofReal r * ENNReal.ofReal (D ^ d / (d * r ^ d)) =
              ENNReal.ofReal (D ^ d / d) * ENNReal.ofReal (r ^ ((1 : ℝ) - d)) := by
            rw [← ENNReal.ofReal_mul hrnn, ← ENNReal.ofReal_mul (by positivity), hid]
          calc (ENNReal.ofReal r * g z) * ENNReal.ofReal (D ^ d / (d * r ^ d))
              = g z * (ENNReal.ofReal r * ENNReal.ofReal (D ^ d / (d * r ^ d))) := by ring
            _ = _ := by rw [hid']; ring

private theorem measurable_segmentSliceWeight_uncurry {g : Mom d → ℝ≥0∞} (hg : Measurable g)
    (x : Mom d) (D : ℝ) :
    Measurable (fun q : ℝ × Mom d => segmentSliceWeight g x D q.1 q.2) := by
  unfold segmentSliceWeight
  have hn : Continuous fun q : ℝ × Mom d => norm (x - q.2) :=
    continuous_norm.comp (continuous_const.sub continuous_snd)
  refine Measurable.ite (measurableSet_le hn.measurable (by fun_prop)) ?_ measurable_const
  exact (ENNReal.measurable_ofReal.comp hn.measurable).mul (hg.comp measurable_snd)

/-- Integration of a weight along the segments from `x` to the points of `S` is bounded by
`D ^ d / d` times the Riesz potential of the weight at `x`. -/
theorem lintegral_lintegral_segment_le_riesz (hd : 0 < d) {g : Mom d → ℝ≥0∞} (hg : Measurable g)
    (x : Mom d) {D : ℝ} (hD : 0 < D) {S : Set (Mom d)} (hS : MeasurableSet S)
    (hSD : ∀ y ∈ S, norm (x - y) ≤ D) :
    ∫⁻ y in S, ∫⁻ s in Ioc (0 : ℝ) 1,
        g (x + s • (y - x)) * ENNReal.ofReal (norm (x - y)) ≤
      ENNReal.ofReal (D ^ d / d) *
        ∫⁻ z, ENNReal.ofReal (norm (x - z) ^ ((1 : ℝ) - d)) * g z := by
  have hn : Continuous fun y : Mom d => norm (x - y) :=
    continuous_norm.comp (continuous_const.sub continuous_id)
  have hmeas1 : Measurable (Function.uncurry fun (y : Mom d) (s : ℝ) =>
      g (x + s • (y - x)) * ENNReal.ofReal (norm (x - y))) := by
    refine Measurable.mul (hg.comp ?_) (ENNReal.measurable_ofReal.comp (hn.measurable.comp
      measurable_fst))
    exact (by fun_prop : Measurable fun q : Mom d × ℝ => x + q.2 • (q.1 - x))
  rw [lintegral_lintegral_swap hmeas1.aemeasurable]
  calc _ ≤ ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (s⁻¹ * (s ^ d)⁻¹) *
          ∫⁻ z, segmentSliceWeight g x D s z :=
        setLIntegral_mono' measurableSet_Ioc fun s hs =>
          lintegral_segment_slice_le hg x hS hSD hs.1
    _ = ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ z, ENNReal.ofReal (s⁻¹ * (s ^ d)⁻¹) *
          segmentSliceWeight g x D s z := by
        refine lintegral_congr fun s => ?_
        rw [lintegral_const_mul _ (measurable_segmentSliceWeight hg x D s)]
    _ = ∫⁻ z, ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (s⁻¹ * (s ^ d)⁻¹) *
          segmentSliceWeight g x D s z := by
        refine lintegral_lintegral_swap ?_
        refine Measurable.aemeasurable ?_
        exact (ENNReal.measurable_ofReal.comp (by fun_prop :
          Measurable fun q : ℝ × Mom d => q.1⁻¹ * (q.1 ^ d)⁻¹)).mul
          (measurable_segmentSliceWeight_uncurry hg x D)
    _ ≤ ∫⁻ z, ENNReal.ofReal (D ^ d / d) *
          (ENNReal.ofReal (norm (x - z) ^ ((1 : ℝ) - d)) * g z) :=
        lintegral_mono fun z => lintegral_time_collapse_pointwise hd hD x z
    _ = _ := by rw [lintegral_const_mul']; exact ENNReal.ofReal_ne_top


end WaveTurbulence.Analysis
