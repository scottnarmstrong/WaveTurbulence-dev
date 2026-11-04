/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic

/-!
# Integrable rational-arc profiles

The log-free Gauss bound is squared and raised to a real exponent. Its
majorant is a translate of `(1+L²|t|)^(-σ)`, whose total mass is `Oσ(L⁻²)`
for `σ>1`. No explicit improper-integral evaluation is needed.
-/

public section

open MeasureTheory

namespace WaveTurbulence.WeylSums

/-- The integrable profile of a rational major arc. -/
@[expose] noncomputable def arcProfile (σ x : ℝ) : ℝ := (1 + |x|) ^ (-σ)

/-- Its finite mass, depending only on the exponent. -/
@[expose] noncomputable def arcProfileMass (σ : ℝ) : ℝ := ∫ x : ℝ, arcProfile σ x

/-- The profile at scale `L` and center `v`. -/
@[expose] noncomputable def scaledArcProfile (L σ v t : ℝ) : ℝ :=
  arcProfile σ (L ^ 2 * (t - v))

theorem arcProfile_nonneg (σ x : ℝ) : 0 ≤ arcProfile σ x :=
  Real.rpow_nonneg (by positivity) _

theorem arcProfileMass_nonneg (σ : ℝ) : 0 ≤ arcProfileMass σ :=
  integral_nonneg (fun x => arcProfile_nonneg σ x)

theorem integrable_arcProfile {σ : ℝ} (hσ : 1 < σ) : Integrable (arcProfile σ) := by
  have hh : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-σ)) :=
    integrable_one_add_norm (by simpa only [Module.finrank_self, Nat.cast_one] using hσ)
  apply hh.congr
  exact Filter.Eventually.of_forall (fun x => by
    change (1 + ‖x‖) ^ (-σ) = (1 + |x|) ^ (-σ)
    rw [Real.norm_eq_abs])

theorem integrable_scaledArcProfile {L σ : ℝ} (hL : 0 < L) (hσ : 1 < σ) (v : ℝ) :
    Integrable (scaledArcProfile L σ v) :=
  ((integrable_arcProfile hσ).comp_mul_left' (sq_pos_of_pos hL).ne').comp_sub_right v

/-- Change of variables gives the exact scale dependence of arc mass. -/
theorem integral_scaledArcProfile {L : ℝ} (hL : 0 < L) (σ v : ℝ) :
    (∫ t : ℝ, scaledArcProfile L σ v t) = arcProfileMass σ / L ^ 2 := by
  change (∫ t : ℝ, arcProfile σ (L ^ 2 * (t - v))) = _
  rw [integral_sub_right_eq_self (fun x : ℝ => arcProfile σ (L ^ 2 * x)) v,
    Measure.integral_comp_mul_left]
  rw [abs_of_pos (inv_pos.mpr (sq_pos_of_pos hL)), smul_eq_mul]
  unfold arcProfileMass
  ring

theorem scaledArcProfile_nonneg (L σ v t : ℝ) : 0 ≤ scaledArcProfile L σ v t :=
  arcProfile_nonneg _ _

/-- The scaled profile can equivalently be written with the distance to its center. -/
theorem scaledArcProfile_eq (L σ v t : ℝ) :
    scaledArcProfile L σ v t = arcProfile σ (L ^ 2 * |t - v|) := by
  simp only [scaledArcProfile, arcProfile, abs_mul, abs_of_nonneg (sq_nonneg L), abs_abs]

end WaveTurbulence.WeylSums
