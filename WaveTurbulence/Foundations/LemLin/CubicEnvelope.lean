/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LemLin.CubicAmplitude
public import WaveTurbulence.Foundations.LemLin.FiniteFubini
public import WaveTurbulence.Foundations.LemLin.FourierEnvelope

/-!
# Integrating the first cubic coordinate

Both source phases have the same coefficient of `x`. Integrating `x`
therefore gives a common Fourier envelope, with all remaining phases of
absolute value one.
-/

public section

namespace WaveTurbulence.LemLin
open MeasureTheory
open scoped FourierTransform

/-- The phase left after integrating `x`. -/
@[expose] def cubicRemainder (kind : CubicPhase) (s : ℝ) (ν : Fin 3 → ℝ) (y z : ℝ) : ℝ :=
  ν 1 * y + ν 2 * z + match kind with
    | .cross => 0
    | .collision => s * z * (y - z)

/-- Exact first-coordinate integration. -/
theorem scalarCubic_inner (kind : CubicPhase) (f : Fin 3 → ScalarCutoff)
    (s t : ℝ) (ν : Fin 3 → ℝ) (y z : ℝ) :
    (∫ x : ℝ, scalarCubicAmplitude kind f s t ![x, y, z] *
      (Real.fourierChar (∑ i, ν i * (![x, y, z] : Fin 3 → ℝ) i) : ℂ)) =
      (f 1 y * f 2 z * (Real.fourierChar (cubicRemainder kind s ν y z) : ℂ)) *
        𝓕 (f 0 : ℝ → ℂ) (-(ν 0 + t * y + s * z)) := by
  rw [Real.fourier_real_eq, ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  dsimp only
  have he : scalarQuadratic kind s t ![x, y, z] +
      (∑ i, ν i * (![x, y, z] : Fin 3 → ℝ) i) =
      cubicRemainder kind s ν y z + (ν 0 + t * y + s * z) * x := by
    cases kind <;> simp [scalarQuadratic, cubicRemainder, Fin.sum_univ_succ] <;> ring
  have hp : cubicProduct f ![x, y, z] = f 0 x * f 1 y * f 2 z := by
    simp [cubicProduct, Fin.prod_univ_succ, mul_assoc]
  simp only [scalarCubicAmplitude, Circle.smul_def, smul_eq_mul]
  rw [mul_assoc (cubicProduct f ![x, y, z]), ← Circle.coe_mul,
    ← AddChar.map_add_eq_mul, he, AddChar.map_add_eq_mul, Circle.coe_mul]
  rw [show -(x * -(ν 0 + t * y + s * z)) = (ν 0 + t * y + s * z) * x by ring]
  rw [hp]
  ring

/-- Modulating the compact amplitude preserves integrability. -/
theorem scalarCubic_integrand_integrable (kind : CubicPhase) (f : Fin 3 → ScalarCutoff)
    (s t : ℝ) (ν : Fin 3 → ℝ) :
    Integrable (fun p => scalarCubicAmplitude kind f s t p *
      (Real.fourierChar (∑ i, ν i * p i) : ℂ)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · apply (scalarCubicAmplitude_contDiff kind f s t).continuous.mul
    fun_prop
  · exact (scalarCubicAmplitude_hasCompactSupport kind f s t).mul_right

/-- The common nonnegative majorant for both scalar cubic phases. -/
theorem norm_scalarCubicIntegral_le_envelope (kind : CubicPhase)
    (f : Fin 3 → ScalarCutoff) (s t : ℝ) (ν : Fin 3 → ℝ) :
    ‖scalarCubicIntegral kind f s t ν‖ ≤ scalarEnvelope (f 0) (f 1) (f 2) (-ν 0) (-t) (-s) := by
  unfold scalarCubicIntegral scalarEnvelope
  rw [integral_fin_three (scalarCubic_integrand_integrable kind f s t ν)]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _))
    (integrable_scalarEnvelope (f 0) (f 1) (f 2) (-ν 0) (-t) (-s)).integral_prod_right
  apply ae_of_all
  intro z
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  apply ae_of_all
  intro y
  dsimp only
  rw [scalarCubic_inner, norm_mul, norm_mul, norm_mul, Circle.norm_coe, mul_one]
  have hf : ((f 0).schwartz : ℝ → ℂ) = (f 0 : ℝ → ℂ) :=
    funext (ScalarCutoff.schwartz_apply (f 0))
  simp only [SchwartzMap.fourier_coe, hf]
  congr 2
  ring_nf

end WaveTurbulence.LemLin
