/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Iterated time integrals: rectangles and triangles

Two Fubini identities for continuous integrands, used to split the diagonal `𝒥ℬ*_𝒬(t, t)` of a dominant
couple by its latest time (DH21 Props 7.8, 7.10, DH23 Prop 6.3):

* `integral_rect_swap`: `∫_a^b ∫_c^d f(u, v) dv du = ∫_c^d ∫_a^b f(u, v) du dv`;
* `integral_triangle_swap'`: `∫_r^t ∫_u^t f(u, v) dv du = ∫_r^t ∫_r^v f(u, v) du dv` for `r ≤ t`.
-/

public section

open MeasureTheory Set Filter intervalIntegral

namespace WaveTurbulence.Cancel

variable {E : Type*} [NormedAddCommGroup E]

theorem integrableOn_uncurry_of_continuous {f : ℝ → ℝ → E} (hf : Continuous (Function.uncurry f))
    (a b c d : ℝ) : IntegrableOn (Function.uncurry f) (uIoc a b ×ˢ uIoc c d) := by
  refine (hf.continuousOn.integrableOn_compact
    ((isCompact_uIcc (a := a) (b := b)).prod (isCompact_uIcc (a := c) (b := d)))).mono_set ?_
  exact prod_mono uIoc_subset_uIcc uIoc_subset_uIcc

variable [NormedSpace ℝ E]

/-- **Fubini on a rectangle** for a continuous integrand. -/
theorem integral_rect_swap [CompleteSpace E] {f : ℝ → ℝ → E} (hf : Continuous (Function.uncurry f)) (a b c d : ℝ) :
    ∫ u in a..b, ∫ v in c..d, f u v = ∫ v in c..d, ∫ u in a..b, f u v :=
  intervalIntegral_intervalIntegral_swap (integrableOn_uncurry_of_continuous hf a b c d)

theorem integral_lower_eq_ite' {f : ℝ → E} (hf : Continuous f) {r u t : ℝ} (h0 : r ≤ u)
    (hu : u ≤ t) : ∫ v in r..u, f v = ∫ v in r..t, if v ≤ u then f v else 0 := by
  have hi : ∀ x y : ℝ, IntervalIntegrable (fun v => if v ≤ u then f v else 0) volume x y := by
    intro x y
    have : (fun v => if v ≤ u then f v else 0) = (Iic u).indicator f := by
      funext v; simp [Set.indicator, Set.mem_Iic]
    rw [this]
    exact ⟨(hf.intervalIntegrable x y).1.indicator measurableSet_Iic,
      (hf.intervalIntegrable x y).2.indicator measurableSet_Iic⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := u) (hi r u) (hi u t)]
  have h1 : ∫ v in r..u, (if v ≤ u then f v else 0) = ∫ v in r..u, f v := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le h0] at hv
    simp [hv.2]
  have h2 : ∫ v in u..t, (if v ≤ u then f v else 0) = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : E)) ?_]
    · simp
    · refine Eventually.of_forall fun v hv => ?_
      rw [uIoc_of_le hu] at hv
      simp [not_le.2 hv.1]
  rw [h1, h2, add_zero]

theorem integral_upper_eq_ite' {f : ℝ → E} (hf : Continuous f) {r v t : ℝ} (h0 : r ≤ v)
    (hv : v ≤ t) : ∫ u in v..t, f u = ∫ u in r..t, if v ≤ u then f u else 0 := by
  have hi : ∀ x y : ℝ, IntervalIntegrable (fun u => if v ≤ u then f u else 0) volume x y := by
    intro x y
    have : (fun u => if v ≤ u then f u else 0) = (Ici v).indicator f := by
      funext u; simp [Set.indicator, Set.mem_Ici]
    rw [this]
    exact ⟨(hf.intervalIntegrable x y).1.indicator measurableSet_Ici,
      (hf.intervalIntegrable x y).2.indicator measurableSet_Ici⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := v) (hi r v) (hi v t)]
  have h1 : ∫ u in r..v, (if v ≤ u then f u else 0) = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : E)) ?_]
    · simp
    · filter_upwards [Measure.ae_ne volume v] with u hne hu
      rw [uIoc_of_le h0] at hu
      simp [not_le.2 (lt_of_le_of_ne hu.2 hne)]
  have h2 : ∫ u in v..t, (if v ≤ u then f u else 0) = ∫ u in v..t, f u := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le hv] at hu
    simp [hu.1]
  rw [h1, h2, zero_add]

/-- **Fubini on the triangle** `r ≤ u ≤ v ≤ t`. -/
theorem integral_triangle_swap' {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f)) {r t : ℝ}
    (ht : r ≤ t) :
    ∫ u in r..t, ∫ v in u..t, f u v = ∫ v in r..t, ∫ u in r..v, f u v := by
  set F : ℝ → ℝ → ℝ := fun u v => if u ≤ v then f u v else 0 with hF
  have hL : ∫ u in r..t, ∫ v in u..t, f u v = ∫ u in r..t, ∫ v in r..t, F u v := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le ht] at hu
    exact integral_upper_eq_ite' (hf.comp (continuous_const.prodMk continuous_id)) hu.1 hu.2
  have hR : ∫ v in r..t, ∫ u in r..v, f u v = ∫ v in r..t, ∫ u in r..t, F u v := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le ht] at hv
    exact integral_lower_eq_ite' (hf.comp (continuous_id.prodMk continuous_const)) hv.1 hv.2
  rw [hL, hR]
  refine intervalIntegral_intervalIntegral_swap ?_
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_Icc (a := r) (b := t))).exists_bound_of_continuousOn
    (hf.continuousOn (s := Icc r t ×ˢ Icc r t))
  have hmeas : Measurable (Function.uncurry F) :=
    Measurable.ite (measurableSet_le measurable_fst measurable_snd) hf.measurable measurable_const
  refine Measure.integrableOn_of_bounded (M := C) ?_ hmeas.aestronglyMeasurable ?_
  · rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_ne_top (by simp [Set.uIoc]) (by simp [Set.uIoc])
  · refine ae_restrict_of_forall_mem (measurableSet_uIoc.prod measurableSet_uIoc) fun p hp => ?_
    rw [Set.uIoc_of_le ht] at hp
    have hp' : p ∈ Icc r t ×ˢ Icc r t := ⟨⟨hp.1.1.le, hp.1.2⟩, ⟨hp.2.1.le, hp.2.2⟩⟩
    simp only [Function.uncurry, hF]
    split_ifs
    · exact hC p hp'
    · simp only [norm_zero]; exact (norm_nonneg _).trans (hC p hp')

end WaveTurbulence.Cancel
