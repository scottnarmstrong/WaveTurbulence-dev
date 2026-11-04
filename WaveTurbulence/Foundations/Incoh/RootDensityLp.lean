/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.RootDensityEndpoints
public import WaveTurbulence.Foundations.Incoh.PhysicalInterpolation
public import WaveTurbulence.Foundations.Incoh.InterpolationExponents

/-!
# Physical interpolation for the actual couple root density

TARGET (incohproof18)–(incohproof20): the input to the landed time-integral
estimate has exponent `1+3η`. Both endpoint bounds are proved for the
literal source marginal, and the final interpolation loss is `8dηg`.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- TARGET's physical `L^(1+3η)` bound for the actual root density. -/
theorem exists_rootDensity_Lp_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        1 ≤ incoherenceCount Q →
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
        ∀ R : RootCoordinates n,
        eLpNorm (R.linkDensity L γ δ Q I) (ENNReal.ofReal (1 + 3 * η)) ≤
          ENNReal.ofReal ((C₀ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 8 * (d : ℝ) * η) * incoherenceCount Q)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_rootDensity_endpoint_bounds d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ η hη hηg δ hδ hδ₁ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ η hη hηg δ hδ hδ₁ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n Q hg hspan I hI hbox R
  have hLone := hL₀.trans hL
  have hLp := zero_lt_one.trans_le hLone
  have hF := (R.integrable_linkDensity hLp γ δ Q hI hbox).aestronglyMeasurable
  have hend := hb L hL n Q hspan I hI hbox R
  have hp : 1 ≤ 1 + 3 * η := by linarith
  have hp₀ : 0 < 1 + 3 * η := by positivity
  have hβ : 0 ≤ 1 - 1 / (1 + 3 * η) := sub_nonneg.mpr ((div_le_one hp₀).mpr hp)
  have hA : 0 ≤ (C₀ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q) := by positivity
  have hdim : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hg' : (1 : ℝ) ≤ incoherenceCount Q := by exact_mod_cast hg
  have hbudget := couple_interpolation_loss_budget hdim hη.le hg'
  apply (eLpNorm_le_of_one_and_scaled_pointwise hF hp hend.1
    (Filter.Eventually.of_forall hend.2)).trans
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hLp.le (2 * (d : ℝ))) hβ,
    ← ENNReal.ofReal_mul hA]
  apply ENNReal.ofReal_le_ofReal
  rw [← Real.rpow_mul hLp.le, mul_assoc, ← Real.rpow_add hLp]
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hLone ?_) (by positivity)
  nlinarith only [hbudget]

end WaveTurbulence.Incoh
