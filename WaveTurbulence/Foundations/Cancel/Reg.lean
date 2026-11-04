/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cancel.Gauss

/-!
# The Gaussian principal value `[G]∫` (DH21 (gausspv))

`greg θ F = ∫ F(x) e^{-πθ²x²} dx`; DH21 (gausspv) (L1713) is `[G]∫ F = lim_{θ→0} greg θ F`.

* `tendsto_greg`: for `F ∈ L¹`, `greg θ F → ∫ F` (DH21 L1714: "if `F ∈ L¹` then `[G]∫` coincides with the
  usual Lebesgue integration").
* `greg_intervalIntegral`: `greg` commutes with an interval integral of a jointly continuous bounded
  integrand (Fubini). This moves the regularization through Volterra operators and kernel compositions.
* `greg_phase`: `greg θ (x ↦ e^{πiεxu}) = gk θ u` for `ε = ±1`.
* `greg_odd`: `greg θ F = 0` for odd `F`.
-/

public section

open MeasureTheory Set Filter Complex intervalIntegral
open scoped Real Topology

namespace WaveTurbulence.Cancel

/-- **The Gaussian regularization** `∫ F(x) e^{-πθ²x²} dx` (DH21 (gausspv)). -/
@[expose] noncomputable def greg (θ : ℝ) (F : ℝ → ℂ) : ℂ := ∫ x, (gw θ x : ℂ) * F x

theorem gw_nonneg (θ x : ℝ) : 0 ≤ gw θ x := (gw_pos θ x).le

theorem tendsto_gw (x : ℝ) : Tendsto (fun θ => gw θ x) (𝓝[>] 0) (𝓝 1) := by
  have h : Continuous fun θ : ℝ => gw θ x := by unfold gw; fun_prop
  have := (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  simpa [gw] using this

/-- **`[G]∫ F = ∫ F` for `F ∈ L¹`** (DH21 L1714). -/
theorem tendsto_greg {F : ℝ → ℂ} (hF : Integrable F) :
    Tendsto (fun θ => greg θ F) (𝓝[>] 0) (𝓝 (∫ x, F x)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖F x‖) ?_ ?_ hF.norm ?_
  · exact Eventually.of_forall fun θ =>
      ((continuous_ofReal.comp (continuous_gw θ)).aestronglyMeasurable).mul hF.aestronglyMeasurable
  · refine Eventually.of_forall fun θ => Eventually.of_forall fun x => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gw_nonneg θ x)]
    exact mul_le_of_le_one_left (norm_nonneg _) (gw_le_one θ x)
  · refine Eventually.of_forall fun x => ?_
    have := ((continuous_ofReal.tendsto 1).comp (tendsto_gw x)).mul_const (F x)
    simpa using this

/-- **Fubini for the regularization of an interval integral.** -/
theorem greg_intervalIntegral {θ : ℝ} (hθ : 0 < θ) {a b C : ℝ} {F : ℝ → ℝ → ℂ}
    (hF : Continuous (Function.uncurry F)) (hb : ∀ x, ∀ s ∈ uIcc a b, ‖F x s‖ ≤ C) :
    greg θ (fun x => ∫ s in a..b, F x s) = ∫ s in a..b, greg θ (fun x => F x s) := by
  unfold greg
  have e : (fun x => (gw θ x : ℂ) * ∫ s in a..b, F x s) =
      fun x => ∫ s in a..b, (gw θ x : ℂ) * F x s := by
    funext x; rw [intervalIntegral.integral_const_mul]
  rw [e]
  refine (intervalIntegral_integral_swap ?_).symm
  -- integrability on `uIoc a b × ℝ`
  have hc : Continuous (Function.uncurry fun (s x : ℝ) => (gw θ x : ℂ) * F x s) :=
    (continuous_ofReal.comp ((continuous_gw θ).comp continuous_snd)).mul
      (hF.comp (continuous_snd.prodMk continuous_fst))
  have hg : Integrable (fun p : ℝ × ℝ => (1 : ℝ) * (C * gw θ p.2))
      ((volume.restrict (uIoc a b)).prod volume) := by
    have : IsFiniteMeasure (volume.restrict (uIoc a b)) :=
      isFiniteMeasure_restrict.2 (by rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top)
    exact Integrable.mul_prod (μ := volume.restrict (uIoc a b)) (integrable_const (1 : ℝ))
      ((integrable_gw hθ).const_mul C)
  refine Integrable.mono' hg hc.aestronglyMeasurable ?_
  rw [show (volume.restrict (uIoc a b)).prod (volume : Measure ℝ) =
      (volume.prod volume).restrict (uIoc a b ×ˢ univ) by
    rw [← Measure.prod_restrict, Measure.restrict_univ],
    ae_restrict_iff' (measurableSet_uIoc.prod MeasurableSet.univ)]
  refine Eventually.of_forall fun p hp => ?_
  simp only [Function.uncurry, one_mul]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gw_nonneg θ _), mul_comm]
  exact mul_le_mul_of_nonneg_right (hb p.2 p.1 (uIoc_subset_uIcc hp.1)) (gw_nonneg θ _)

/-- **The regularized phase** `greg θ (x ↦ e^{πiεxu}) = gk θ u` for `ε = ±1`. -/
theorem greg_phase {θ : ℝ} (hθ : 0 < θ) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (u : ℝ) :
    greg θ (fun x => cexp (π * I * (ε * x * u))) = gk θ u := by
  have h := ft_gw hθ (ε * u)
  have hg : gk θ (ε * u) = gk θ u := by
    unfold gk; congr 3; rcases hε with rfl | rfl <;> simp
  rw [hg] at h
  rw [← h, greg]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [mul_comm]
  congr 2
  push_cast; ring

/-- **The regularization of an odd function vanishes.** -/
theorem greg_odd {θ : ℝ} {F : ℝ → ℂ} (hodd : ∀ x, F (-x) = -F x) : greg θ F = 0 := by
  unfold greg
  have h := integral_neg_eq_self (fun x => (gw θ x : ℂ) * F x) volume
  have e : (fun x => (gw θ (-x) : ℂ) * F (-x)) = fun x => -((gw θ x : ℂ) * F x) := by
    funext x; rw [hodd, show gw θ (-x) = gw θ x by simp [gw]]; ring
  simp only [e, MeasureTheory.integral_neg] at h
  have : (2 : ℂ) * ∫ x, (gw θ x : ℂ) * F x = 0 := by linear_combination -h
  simpa using this

theorem integrable_gw_mul {θ : ℝ} (hθ : 0 < θ) {F : ℝ → ℂ} (hF : Continuous F) {C : ℝ}
    (hb : ∀ x, ‖F x‖ ≤ C) : Integrable fun x => (gw θ x : ℂ) * F x := by
  refine Integrable.mono' ((integrable_gw hθ).mul_const C)
    ((continuous_ofReal.comp (continuous_gw θ)).mul hF).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gw_nonneg θ x)]
  exact mul_le_mul_of_nonneg_left (hb x) (gw_nonneg θ x)

theorem greg_add {θ : ℝ} {F G : ℝ → ℂ} (hF : Integrable fun x => (gw θ x : ℂ) * F x)
    (hG : Integrable fun x => (gw θ x : ℂ) * G x) : greg θ (F + G) = greg θ F + greg θ G := by
  unfold greg
  rw [← integral_add hF hG]
  congr 1; funext x; simp only [Pi.add_apply]; ring

theorem greg_sub {θ : ℝ} {F G : ℝ → ℂ} (hF : Integrable fun x => (gw θ x : ℂ) * F x)
    (hG : Integrable fun x => (gw θ x : ℂ) * G x) : greg θ (F - G) = greg θ F - greg θ G := by
  unfold greg
  rw [← integral_sub hF hG]
  congr 1; funext x; simp only [Pi.sub_apply]; ring

theorem greg_const_mul (θ : ℝ) (c : ℂ) (F : ℝ → ℂ) :
    greg θ (fun x => c * F x) = c * greg θ F := by
  unfold greg
  rw [← MeasureTheory.integral_const_mul]
  congr 1; funext x; ring

theorem greg_mul_const (θ : ℝ) (c : ℂ) (F : ℝ → ℂ) :
    greg θ (fun x => F x * c) = greg θ F * c := by
  unfold greg
  rw [← MeasureTheory.integral_mul_const]
  congr 1; funext x; ring

end WaveTurbulence.Cancel
