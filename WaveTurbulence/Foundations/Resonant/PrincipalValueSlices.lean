/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKE.Characterization
public import WaveTurbulence.Foundations.Resonant.PrincipalValueOneDim

/-!
# Slicing the truncated inverse energy resonance

The energy resonance in the collision parametrization is `-2⟨ℓ,x⟩`.
For `ℓ ≠ 0`, disintegration along `ℓ` turns its truncated inverse into
`-(2|ℓ|)⁻¹` times the one-dimensional principal-value truncation of the slice.
-/

public section

open MeasureTheory Filter Topology Set
open scoped InnerProductSpace

namespace WaveTurbulence.Resonant

variable {d : ℕ}

namespace IsPVCutoff

variable {χ : ℝ → ℝ}

/-- The finite truncated reciprocal is bounded on the entire line. -/
theorem exists_bound_div (hχ : IsPVCutoff χ) (μ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, |(1 - χ (μ * u)) / u| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hχ.continuous_div μ).continuousOn (s := Icc (-1 : ℝ) 1))
  obtain ⟨D, hD⟩ := hχ.cont.bounded_above_of_compact_support hχ.compact
  refine ⟨max (max C (1 + D)) 0, le_max_right _ _, fun u => ?_⟩
  by_cases hu : |u| ≤ 1
  · have hcu : |(1 - χ (μ * u)) / u| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC u (abs_le.mp hu)
    exact hcu.trans ((le_max_left _ _).trans (le_max_left _ _))
  · have hu1 : 1 ≤ |u| := (lt_of_not_ge hu).le
    calc |(1 - χ (μ * u)) / u| = |1 - χ (μ * u)| / |u| := abs_div _ _
      _ ≤ |1 - χ (μ * u)| := div_le_self (abs_nonneg _) hu1
      _ ≤ 1 + D := (abs_sub _ _).trans (by simpa using add_le_add_left (hD (μ * u)) 1)
      _ ≤ _ := (le_max_right _ _).trans (le_max_left _ _)

end IsPVCutoff

/-- Finite truncation of the inverse energy resonance for a fixed outer momentum. -/
@[expose] noncomputable def energyInvInner (χ : ℝ → ℝ) (μ : ℝ)
    (F : Mom d → Mom d → ℝ) (ℓ : Mom d) : ℝ :=
  ∫ x : Mom d, F ℓ x * ((1 - χ (μ * (-(2 * ⟪ℓ, x⟫_ℝ)))) / (-(2 * ⟪ℓ, x⟫_ℝ)))

/-- Every finite truncated inner integral is integrable. -/
theorem integrable_energyInvInner
    {F : Mom d → Mom d → ℝ} {A : Mom d → ℝ} {b : Mom d → Mom d} {M : ℝ}
    (hK : DeltaKernel F A b M) {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) (μ : ℝ) (ℓ : Mom d) :
    Integrable (fun x : Mom d => F ℓ x *
      ((1 - χ (μ * (-(2 * ⟪ℓ, x⟫_ℝ)))) / (-(2 * ⟪ℓ, x⟫_ℝ)))) := by
  obtain ⟨C, _, hC⟩ := hχ.exists_bound_div μ
  refine (hK.integrable_right ℓ).mul_bdd (c := C) ?_ (Eventually.of_forall fun x => ?_)
  · exact ((hχ.continuous_div μ).comp
      ((continuous_const.mul (continuous_const.inner continuous_id)).neg)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact hC _

/-- Exact slice identity, including the sign and normalization of the frozen
energy resonance. -/
theorem energyInvInner_eq
    {F : Mom d → Mom d → ℝ} {A : Mom d → ℝ} {b : Mom d → Mom d} {M : ℝ}
    (hK : DeltaKernel F A b M) {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) (μ : ℝ)
    {ℓ : Mom d} (hℓ : ℓ ≠ 0) :
    energyInvInner χ μ F ℓ = -(2 * ‖ℓ‖)⁻¹ *
      pvTruncation χ (μ * (2 * ‖ℓ‖)) (sliceInt F ℓ) := by
  rw [energyInvInner, integral_eq_integral_slice hℓ (integrable_energyInvInner hK hχ μ ℓ)]
  have hin : ∀ t (w : ↥(ℝ ∙ ℓ)ᗮ), ⟪ℓ, t • unitVec ℓ + (w : Mom d)⟫_ℝ = t * ‖ℓ‖ := by
    intro t w
    rw [inner_add_right, inner_smul_right, inner_unitVec_self, inner_eq_zero_of_mem_perp w,
      add_zero]
  simp_rw [hin, integral_mul_const]
  rw [pvTruncation, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [sliceInt]
  rw [mul_neg, hχ.even]
  simp only [div_eq_mul_inv, inv_neg, mul_inv_rev]
  ring_nf

end WaveTurbulence.Resonant
