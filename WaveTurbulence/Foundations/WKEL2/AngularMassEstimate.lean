/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.AngularSchur
public import WaveTurbulence.Foundations.WKEL2.AngularProduct
public import WaveTurbulence.Foundations.WKEL2.AngularCauchyAlgebra
public import WaveTurbulence.Foundations.WKEL2.RadialCauchyENN

/-!
# The angular estimate for the second loss operator
-/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

attribute [local instance] referenceMeasureSpace referenceBorelSpace

/-- Uniform bound for the product of the two absolute ray masses. -/
theorem exists_angular_mass_bound (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ e : Mom d, ‖e‖ = 1 → ∀ f g : Mom d → ℝ,
      Measurable f → Measurable g → MemLp (weightedFunction s f) 2 →
      MemLp (weightedFunction s g) 2 → ∀ k : Mom d,
        (∫⁻ p, radialMass f k p.1 * radialMass g k p.2 ∂angularMeasure e) ≤
          ENNReal.ofReal C * ENNReal.ofReal (weightedL2Norm s f * weightedL2Norm s g) := by
  obtain ⟨C, hC, hbound⟩ := exists_angular_schur_energy_bound hd s hs
  refine ⟨C, hC, fun e he f g hf hg hLf hLg k => ?_⟩
  let μ := (volume : Measure (Mom d)).toSphere.prod
    (volume : Measure ↥(ℝ ∙ e)ᗮ).toSphere
  let U : Mom d × Mom d → ℝ≥0∞ := fun p =>
    radialEnergy s f k p.1 * ENNReal.ofReal (radialWeight d s k p.2)
  let V : Mom d × Mom d → ℝ≥0∞ := fun p =>
    radialEnergy s g k p.2 * ENNReal.ofReal (radialWeight d s k p.1)
  have hA := (measurable_radialWeight_direction s k).ennreal_ofReal
  have hU : Measurable U :=
    ((measurable_radialEnergy s hf k).comp measurable_fst).mul (hA.comp measurable_snd)
  have hV : Measurable V :=
    ((measurable_radialEnergy s hg k).comp measurable_snd).mul (hA.comp measurable_fst)
  have hMf : Measurable (fun p : Mom d × Mom d => radialMass f k p.1 * radialMass g k p.2) :=
    ((measurable_radialMass hf k).comp measurable_fst).mul
      ((measurable_radialMass hg k).comp measurable_snd)
  have hpoint (p : sphere (0 : Mom d) 1 × sphere (0 : ↥(ℝ ∙ e)ᗮ) 1) :
      radialMass f k (angularPair e p).1 * radialMass g k (angularPair e p).2 ≤
        (U (angularPair e p)) ^ ((1 : ℝ) / 2) *
          (V (angularPair e p)) ^ ((1 : ℝ) / 2) := by
    obtain ⟨h1, h2⟩ := angularPair_norms e p
    have h := mul_le_mul' (radialMass_le_energy_weight hd s hs hf k _ h1)
      (radialMass_le_energy_weight hd s hs hg k _ h2)
    simpa only [ennreal_schur_pairing, U, V] using h
  have hconj : (2 : ℝ).HolderConjugate 2 := by rw [Real.holderConjugate_iff]; norm_num
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj
    ((measurable_angularIntegrand e hU).pow_const ((1 : ℝ) / 2)).aemeasurable
    ((measurable_angularIntegrand e hV).pow_const ((1 : ℝ) / 2)).aemeasurable
  simp only [ennreal_half_sq] at hHolder
  have hUi : (∫⁻ p, U (angularPair e p) ∂μ) ≤
      ENNReal.ofReal C * ENNReal.ofReal ((weightedL2Norm s f) ^ 2) := by
    rw [lintegral_angularProduct he (by omega) hU]
    exact hbound e he f hf hLf k
  have hVi : (∫⁻ p, V (angularPair e p) ∂μ) ≤
      ENNReal.ofReal C * ENNReal.ofReal ((weightedL2Norm s g) ^ 2) := by
    rw [lintegral_angularProduct he (by omega) hV]
    have hW : Measurable (fun p : Mom d × Mom d =>
        radialEnergy s g k p.1 * ENNReal.ofReal (radialWeight d s k p.2)) :=
      ((measurable_radialEnergy s hg k).comp measurable_fst).mul (hA.comp measurable_snd)
    have hswap : (∫⁻ p, V p ∂angularMeasure e) =
        ∫⁻ p, radialEnergy s g k p.1 * ENNReal.ofReal (radialWeight d s k p.2)
          ∂angularMeasure e := by
      simpa only [V] using lintegral_angular_swap he (by omega) hW
    rw [hswap]
    exact hbound e he g hg hLg k
  calc
    _ = ∫⁻ p, radialMass f k (angularPair e p).1 * radialMass g k (angularPair e p).2 ∂μ :=
      (lintegral_angularProduct he (by omega) hMf).symm
    _ ≤ _ := lintegral_mono hpoint
    _ ≤ _ := hHolder
    _ ≤ (ENNReal.ofReal C * ENNReal.ofReal ((weightedL2Norm s f) ^ 2)) ^ ((1 : ℝ) / 2) *
        (ENNReal.ofReal C * ENNReal.ofReal ((weightedL2Norm s g) ^ 2)) ^ ((1 : ℝ) / 2) :=
      mul_le_mul' (ENNReal.rpow_le_rpow hUi (by norm_num))
        (ENNReal.rpow_le_rpow hVi (by norm_num))
    _ = _ := ennreal_schur_norm_constant _ _ _ (weightedL2Norm_nonneg _ _) (weightedL2Norm_nonneg _ _)

end WaveTurbulence.WKEL2
