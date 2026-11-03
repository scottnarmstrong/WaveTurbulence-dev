/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.IJI5

/-!
# Superposition kernels: continuity, compositions with single `J` kernels, Fubini
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

attribute [local instance] isFiniteMeasure_volume_unit

section Superposition

variable {Z : Type*} [MeasureSpace Z] [SFinite (volume : Measure Z)]

theorem integral_unitProd (g : Unit × Z → ℂ) : ∫ p, g p = ∫ z, g ((), z) := by
  rw [Measure.volume_eq_prod, show (volume : Measure Unit) = Measure.dirac () from rfl,
    Measure.dirac_prod]
  exact integral_map_equiv (MeasurableEquiv.punitProd (α := Z)).symm g

theorem integral_prodUnit' (g : Z × Unit → ℂ) : ∫ p, g p = ∫ z, g (z, ()) := by
  rw [Measure.volume_eq_prod, show (volume : Measure Unit) = Measure.dirac () from rfl,
    Measure.prod_dirac]
  exact integral_map_equiv (MeasurableEquiv.prodPUnit (α := Z)).symm g

/-- The superposition `∫ f(z) J_{L; u(z), v(z)} dz`. -/
@[expose] noncomputable def sp (f : Z → ℂ) (L : ℝ) (u v : Z → ℝ) (t s : ℝ) : ℂ :=
  ∫ z, f z * jker L (u z) (v z) t s

theorem continuous_sp {f : Z → ℂ} (hf : Integrable f) (L : ℝ) {u v : Z → ℝ}
    (hu : Measurable u) (hv : Measurable v) :
    Continuous fun p : ℝ × ℝ => sp f L u v p.1 p.2 := by
  unfold sp
  refine continuous_of_dominated (bound := fun z => ‖f z‖) (fun p => ?_) (fun p => ?_)
    hf.norm (Eventually.of_forall fun z => ?_)
  · exact hf.aestronglyMeasurable.mul ((continuous_jker_coeff L p.1 p.2).measurable.comp
      (hu.prodMk hv)).aestronglyMeasurable
  · exact Eventually.of_forall fun z => by rw [norm_mul, norm_jker, mul_one]
  · exact continuous_const.mul (continuous_jker _ _ _)

/-- `J_{L₁; a, b} (∫ f J_{L₂; u, v})`. -/
theorem kcomp_jker_sp {f : Z → ℂ} (hf : Integrable f) (L₁ a b L₂ : ℝ) {u v : Z → ℝ}
    (hu : Measurable u) (hv : Measurable v) {t s : ℝ} (hst : s ≤ t) :
    kcomp (jker L₁ a b) (sp f L₂ u v) t s =
      ∫ z, f z * kcomp (jker L₁ a b) (jker L₂ (u z) (v z)) t s := by
  have h := kcomp_integral_jker (Z₁ := Unit) (f₁ := fun _ => (1 : ℂ)) (integrable_const _) hf
    L₁ L₂ (u₁ := fun _ => a) (v₁ := fun _ => b) measurable_const measurable_const hu hv hst
  have e : (fun t s => ∫ _ : Unit, (1 : ℂ) * jker L₁ a b t s) = jker L₁ a b := by
    funext t s; rw [integral_unit, one_mul]
  rw [e] at h
  rw [show sp f L₂ u v = fun t s => ∫ z, f z * jker L₂ (u z) (v z) t s from rfl, h,
    integral_unitProd]
  simp only [one_mul]

/-- `(∫ f J_{L₁; u, v}) J_{L₂; a, b}`. -/
theorem kcomp_sp_jker {f : Z → ℂ} (hf : Integrable f) (L₁ L₂ a b : ℝ) {u v : Z → ℝ}
    (hu : Measurable u) (hv : Measurable v) {t s : ℝ} (hst : s ≤ t) :
    kcomp (sp f L₁ u v) (jker L₂ a b) t s =
      ∫ z, f z * kcomp (jker L₁ (u z) (v z)) (jker L₂ a b) t s := by
  have h := kcomp_integral_jker (Z₂ := Unit) (f₂ := fun _ => (1 : ℂ)) hf (integrable_const _)
    L₁ L₂ (u₂ := fun _ => a) (v₂ := fun _ => b) hu hv measurable_const measurable_const hst
  have e : (fun t s => ∫ _ : Unit, (1 : ℂ) * jker L₂ a b t s) = jker L₂ a b := by
    funext t s; rw [integral_unit, one_mul]
  rw [e] at h
  rw [show sp f L₁ u v = fun t s => ∫ z, f z * jker L₁ (u z) (v z) t s from rfl, h,
    integral_prodUnit']
  simp only [mul_one]

/-- Linearity of the composition in the first kernel. -/
theorem kcomp_add_sub {K₁ K₂ K₃ L : ℝ → ℝ → ℂ} (h₁ : Continuous fun p : ℝ × ℝ => K₁ p.1 p.2)
    (h₂ : Continuous fun p : ℝ × ℝ => K₂ p.1 p.2) (h₃ : Continuous fun p : ℝ × ℝ => K₃ p.1 p.2)
    (hL : Continuous fun p : ℝ × ℝ => L p.1 p.2) (t s : ℝ) :
    kcomp (fun t s => K₁ t s + K₂ t s - K₃ t s) L t s =
      kcomp K₁ L t s + kcomp K₂ L t s - kcomp K₃ L t s := by
  have hc : ∀ {K : ℝ → ℝ → ℂ}, (Continuous fun p : ℝ × ℝ => K p.1 p.2) →
      IntervalIntegrable (fun z => K t z * L z s) volume s t := fun {K} hK =>
    ((hK.comp (continuous_const.prodMk continuous_id)).mul
      (hL.comp (continuous_id.prodMk continuous_const))).intervalIntegrable _ _
  simp only [kcomp, add_mul, sub_mul]
  rw [intervalIntegral.integral_sub ((hc h₁).add (hc h₂)) (hc h₃),
    intervalIntegral.integral_add (hc h₁) (hc h₂)]

/-- Composition with a constant multiple of a kernel. -/
theorem kcomp_const_mul (c : ℂ) (K L : ℝ → ℝ → ℂ) (t s : ℝ) :
    kcomp (fun t s => c * K t s) L t s = c * kcomp K L t s := by
  simp only [kcomp, mul_assoc]
  exact intervalIntegral.integral_const_mul _ _

end Superposition

end WaveTurbulence.ClassJR
