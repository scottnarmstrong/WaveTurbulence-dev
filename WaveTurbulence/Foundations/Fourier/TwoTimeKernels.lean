/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.SignedIntervalKernel
public import WaveTurbulence.Foundations.Fourier.TwoCoordinateIntegration
public import WaveTurbulence.Foundations.Fourier.RectanglePrimitive
import Mathlib.Tactic

/-!
# Measurable bounded kernels for the two time primitives

These real-space kernels support the finite-norm extension in A.2. They
retain the exact oriented intervals, including the reversed triangle.
-/

public section

open MeasureTheory

namespace WaveTurbulence.Fourier

/-- The rectangle's real-space kernel. -/
@[expose] noncomputable def rectangleTimeKernel (t v : Fin 2 → ℝ) : ℂ :=
  signedIntervalKernel 0 (t 0) (v 0) * signedIntervalKernel 0 (t 1) (v 1)

/-- The triangle's real-space kernel. -/
@[expose] noncomputable def triangleTimeKernel (t v : Fin 2 → ℝ) : ℂ :=
  signedIntervalKernel (t 1) (t 0) (v 0) * signedIntervalKernel (t 1) (v 0) (v 1)

/-- The rectangle kernel is jointly measurable. -/
theorem rectangleTimeKernel_measurable :
    Measurable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => rectangleTimeKernel p.1 p.2) := by
  apply Measurable.mul
    (signedIntervalKernel_measurable.comp (show Measurable
      (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => ((0, p.1 0), p.2 0)) by fun_prop))
    (signedIntervalKernel_measurable.comp (show Measurable
      (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => ((0, p.1 1), p.2 1)) by fun_prop))

/-- The triangle kernel is jointly measurable. -/
theorem triangleTimeKernel_measurable :
    Measurable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => triangleTimeKernel p.1 p.2) := by
  apply Measurable.mul
    (signedIntervalKernel_measurable.comp (show Measurable
      (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => ((p.1 1, p.1 0), p.2 0)) by fun_prop))
    (signedIntervalKernel_measurable.comp (show Measurable
      (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => ((p.1 1, p.2 0), p.2 1)) by fun_prop))

/-- Both kernel factors have magnitude at most one. -/
theorem norm_rectangleTimeKernel_le (t v : Fin 2 → ℝ) : ‖rectangleTimeKernel t v‖ ≤ 1 := by
  rw [rectangleTimeKernel, norm_mul]
  exact (mul_le_mul (norm_signedIntervalKernel_le _ _ _) (norm_signedIntervalKernel_le _ _ _)
    (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

/-- The reversed triangle has the same unit kernel bound. -/
theorem norm_triangleTimeKernel_le (t v : Fin 2 → ℝ) : ‖triangleTimeKernel t v‖ ≤ 1 := by
  rw [triangleTimeKernel, norm_mul]
  exact (mul_le_mul (norm_signedIntervalKernel_le _ _ _) (norm_signedIntervalKernel_le _ _ _)
    (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

/-- Bochner Fubini in the coordinate-time convention. -/
theorem integral_two_coordinates {f : (Fin 2 → ℝ) → ℂ} (hf : Integrable f) :
    (∫ x, f x) = ∫ u : ℝ, ∫ v : ℝ, f ![u, v] := by
  have hm := volume_preserving_finTwoArrow ℝ
  have hi := hm.symm.integrable_comp_of_integrable hf
  calc
    _ = ∫ z : ℝ × ℝ, f (MeasurableEquiv.finTwoArrow.symm z) := (hm.symm.integral_comp' f).symm
    _ = ∫ z : ℝ × ℝ, f ![z.1, z.2] := by congr 1
    _ = _ := integral_prod _ hi

/-- A bounded measurable kernel times an integrable amplitude is integrable. -/
theorem integrable_timeKernel_mul {K : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℂ}
    (hK : Measurable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => K p.1 p.2))
    (hKn : ∀ t v, ‖K t v‖ ≤ 1) {A : (Fin 2 → ℝ) → ℂ} (hA : Integrable A)
    (t : Fin 2 → ℝ) : Integrable (fun v => K t v * A v) :=
  hA.bdd_mul (hK.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (ae_of_all _ (hKn t))

/-- The real-space rectangle kernel represents the literal rectangular primitive. -/
theorem integral_rectangleTimeKernel_mul {A : (Fin 2 → ℝ) → ℂ} (hA : Integrable A)
    (t : Fin 2 → ℝ) : (∫ v, rectangleTimeKernel t v * A v) = rectanglePrimitive A t := by
  rw [integral_two_coordinates (integrable_timeKernel_mul rectangleTimeKernel_measurable
    norm_rectangleTimeKernel_le hA t)]
  simp only [rectangleTimeKernel, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp_rw [mul_assoc, integral_const_mul,
    integral_signedIntervalKernel_mul]
  rfl

/-- The real-space triangle kernel represents both orientations of the literal triangle. -/
theorem integral_triangleTimeKernel_mul {A : (Fin 2 → ℝ) → ℂ} (hA : Integrable A)
    (t : Fin 2 → ℝ) : (∫ v, triangleTimeKernel t v * A v) =
      ∫ u in t 1..t 0, ∫ v in t 1..u, A ![u, v] := by
  rw [integral_two_coordinates (integrable_timeKernel_mul triangleTimeKernel_measurable
    norm_triangleTimeKernel_le hA t)]
  simp only [triangleTimeKernel, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp_rw [mul_assoc, integral_const_mul,
    integral_signedIntervalKernel_mul]

end WaveTurbulence.Fourier
