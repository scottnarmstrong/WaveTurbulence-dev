/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LemLin.CubicEnvelope
public import WaveTurbulence.Foundations.LemLin.CubicMatrix

/-!
# Scalar stationary phase for both cubic forms

Integrate `x` first. The `t` direction integrates the resulting Fourier
transform in `y`, and the `s` direction integrates it in `z`. This proves
the uniform `(1+|s|+|t|)⁻¹` gain with constants depending only on the cutoffs.
-/

public section

namespace WaveTurbulence.LemLin
open MeasureTheory
open scoped FourierTransform

/-- The fixed mass controlling one bilinear direction. -/
@[expose] noncomputable def scalarSlopeMass (f g h : ScalarCutoff) : ℝ :=
  (∫ z : ℝ, ‖h z‖) * SchwartzMap.seminorm ℂ 0 0 g.schwartz *
    ∫ u : ℝ, ‖𝓕 f.schwartz u‖

theorem scalarSlopeMass_nonneg (f g h : ScalarCutoff) : 0 ≤ scalarSlopeMass f g h := by
  unfold scalarSlopeMass
  exact mul_nonneg (mul_nonneg (integral_nonneg (fun _ => norm_nonneg _))
    (apply_nonneg _ _)) (integral_nonneg (fun _ => norm_nonneg _))

/-- The reciprocal slope estimate, with no division and including zero slope. -/
theorem scalarEnvelope_slope_mul_le (f g h : ScalarCutoff) (A B C : ℝ) :
    |B| * scalarEnvelope f g h A B C ≤ scalarSlopeMass f g h := by
  by_cases hB : B = 0
  · simpa only [hB, abs_zero, zero_mul] using scalarSlopeMass_nonneg f g h
  have hb := scalarEnvelope_le_slope f g h A C hB
  calc
    _ ≤ |B| * ((∫ z : ℝ, ‖h z‖) * SchwartzMap.seminorm ℂ 0 0 g.schwartz *
        (|B|⁻¹ * ∫ u : ℝ, ‖𝓕 f.schwartz u‖)) :=
      mul_le_mul_of_nonneg_left hb (abs_nonneg B)
    _ = _ := by
      unfold scalarSlopeMass
      field_simp [abs_ne_zero.mpr hB]

/-- A fixed constant valid for both source quadratic forms. -/
@[expose] noncomputable def scalarStationaryConstant (f : Fin 3 → ScalarCutoff) : ℝ :=
  (∫ x : ℝ, ‖f 0 x‖) * (∫ y : ℝ, ‖f 1 y‖) * (∫ z : ℝ, ‖f 2 z‖) +
    scalarSlopeMass (f 0) (f 1) (f 2) + scalarSlopeMass (f 0) (f 2) (f 1)

theorem scalarStationaryConstant_nonneg (f : Fin 3 → ScalarCutoff) :
    0 ≤ scalarStationaryConstant f := by
  unfold scalarStationaryConstant
  exact add_nonneg (add_nonneg (by positivity) (scalarSlopeMass_nonneg _ _ _))
    (scalarSlopeMass_nonneg _ _ _)

/-- TARGET `lemcubic0`: the scalar stationary estimate, uniform in all frequencies. -/
theorem scalarCubic_stationary (kind : CubicPhase) (f : Fin 3 → ScalarCutoff)
    (s t : ℝ) (ν : Fin 3 → ℝ) :
    cubicScale s t * ‖scalarCubicIntegral kind f s t ν‖ ≤ scalarStationaryConstant f := by
  have he := norm_scalarCubicIntegral_le_envelope kind f s t ν
  have hp := he.trans (scalarEnvelope_le_mass (f 0) (f 1) (f 2) (-ν 0) (-t) (-s))
  have ht : |t| * ‖scalarCubicIntegral kind f s t ν‖ ≤ scalarSlopeMass (f 0) (f 1) (f 2) := by
    have hb := scalarEnvelope_slope_mul_le (f 0) (f 1) (f 2) (-ν 0) (-t) (-s)
    rw [abs_neg] at hb
    exact (mul_le_mul_of_nonneg_left he (abs_nonneg t)).trans hb
  have hs : |s| * ‖scalarCubicIntegral kind f s t ν‖ ≤ scalarSlopeMass (f 0) (f 2) (f 1) := by
    rw [scalarEnvelope_swap] at he
    have hb := scalarEnvelope_slope_mul_le (f 0) (f 2) (f 1) (-ν 0) (-s) (-t)
    rw [abs_neg] at hb
    exact (mul_le_mul_of_nonneg_left he (abs_nonneg s)).trans hb
  unfold cubicScale scalarStationaryConstant
  nlinarith only [hp, ht, hs]

end WaveTurbulence.LemLin
