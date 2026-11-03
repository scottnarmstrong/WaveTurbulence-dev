/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

/-!
# Integrating the anisotropic kernel along one coordinate

The identity `∫ (t²+r²)^(-p/2) dt = r^(1-p) ∫ (1+t²)^(-p/2) dt`
for positive transverse radius is used in the far-field M₁ estimate.
-/

public section

noncomputable section

open MeasureTheory

namespace WaveTurbulence.WKEL2

/-- The finite scalar slice mass for `p > 1`. -/
@[expose] def scalarSliceMass (p : ℝ) : ℝ := ∫ t : ℝ, (1 + t ^ 2) ^ (-p / 2)

theorem integrable_scalarSlice (p : ℝ) (hp : 1 < p) :
    Integrable (fun t : ℝ => (1 + t ^ 2) ^ (-p / 2)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
    (r := p) (by simpa using hp)
  simpa only [Real.norm_eq_abs, sq_abs] using h

theorem scalarSliceMass_nonneg (p : ℝ) : 0 ≤ scalarSliceMass p :=
  integral_nonneg fun _ => Real.rpow_nonneg (by positivity) _

/-- Pointwise scaling identity on the scalar slice. -/
theorem scalarSlice_scale (p t r : ℝ) (hr : 0 < r) :
    (t ^ 2 + r ^ 2) ^ (-p / 2) = r ^ (-p) * (1 + (r⁻¹ * t) ^ 2) ^ (-p / 2) := by
  have he : t ^ 2 + r ^ 2 = r ^ 2 * (1 + (r⁻¹ * t) ^ 2) := by
    field_simp [hr.ne']
    ring
  rw [he, Real.mul_rpow (sq_nonneg _) (by positivity), ← Real.rpow_natCast r 2,
    ← Real.rpow_mul hr.le]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * (-p / 2) = -p by ring]

/-- Integrability and exact slice mass, uniform in positive transverse radii. -/
theorem integrable_integral_scalarSlice (p : ℝ) (hp : 1 < p) (r : ℝ) (hr : 0 < r) :
    Integrable (fun t : ℝ => (t ^ 2 + r ^ 2) ^ (-p / 2)) ∧
      (∫ t : ℝ, (t ^ 2 + r ^ 2) ^ (-p / 2)) = r ^ (1 - p) * scalarSliceMass p := by
  have hpoint : (fun t : ℝ => (t ^ 2 + r ^ 2) ^ (-p / 2)) =
      (fun t => r ^ (-p) * (1 + (r⁻¹ * t) ^ 2) ^ (-p / 2)) :=
    funext fun t => scalarSlice_scale p t r hr
  rw [hpoint]
  refine ⟨((integrable_scalarSlice p hp).comp_mul_left' (inv_ne_zero hr.ne')).const_mul _, ?_⟩
  have hscale := Measure.integral_comp_mul_left (fun t : ℝ => (1 + t ^ 2) ^ (-p / 2)) r⁻¹
  simp only [inv_inv, abs_of_pos hr, smul_eq_mul] at hscale
  rw [integral_const_mul, hscale]
  have hprod : r ^ (-p) * r = r ^ (1 - p) := by
    calc
      _ = r ^ (-p) * r ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = r ^ (-p + 1) := (Real.rpow_add hr _ _).symm
      _ = _ := by congr 1; ring
  change r ^ (-p) * (r * scalarSliceMass p) = r ^ (1 - p) * scalarSliceMass p
  rw [← mul_assoc, hprod]

end WaveTurbulence.WKEL2
