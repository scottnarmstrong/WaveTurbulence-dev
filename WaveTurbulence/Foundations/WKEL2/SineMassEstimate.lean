/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.SineSchurEnergy
public import WaveTurbulence.Foundations.WKEL2.SineCauchyAlgebra
public import WaveTurbulence.Foundations.WKEL2.RadialCauchyENN

/-!
# The full-sphere mass estimate with the sine denominator

The last angular estimate in research-note Proposition 6.
-/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Uniform bilinear ray-mass estimate against the inverse sine kernel. -/
theorem exists_sine_mass_bound (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f g : Mom d → ℝ, Measurable f → Measurable g →
      MemLp (weightedFunction s f) 2 → MemLp (weightedFunction s g) 2 → ∀ k : Mom d,
      (∫⁻ p : sphere (0 : Mom d) 1 × sphere (0 : Mom d) 1,
        radialMass f k p.1.1 * radialMass g k p.2.1 * ENNReal.ofReal (angularSineInv p.1.1 p.2.1)
        ∂((volume : Measure (Mom d)).toSphere.prod (volume : Measure (Mom d)).toSphere)) ≤
      ENNReal.ofReal C * ENNReal.ofReal (weightedL2Norm s f * weightedL2Norm s g) := by
  obtain ⟨C, hC, hb⟩ := exists_sine_schur_energy_bound hd s hs
  refine ⟨C, hC, fun f g hf hg hLf hLg k => ?_⟩
  let ν := (volume : Measure (Mom d)).toSphere
  let μ := ν.prod ν
  let K : sphere (0 : Mom d) 1 × sphere (0 : Mom d) 1 → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (angularSineInv p.1.1 p.2.1)
  let U : sphere (0 : Mom d) 1 × sphere (0 : Mom d) 1 → ℝ≥0∞ :=
    fun p => radialEnergy s f k p.1.1 * ENNReal.ofReal (radialWeight d s k p.2.1) * K p
  let V : sphere (0 : Mom d) 1 × sphere (0 : Mom d) 1 → ℝ≥0∞ :=
    fun p => radialEnergy s g k p.2.1 * ENNReal.ofReal (radialWeight d s k p.1.1) * K p
  have hEf : Measurable (fun θ : sphere (0 : Mom d) 1 => radialEnergy s f k θ.1) :=
    (measurable_radialEnergy s hf k).comp measurable_subtype_coe
  have hEg : Measurable (fun θ : sphere (0 : Mom d) 1 => radialEnergy s g k θ.1) :=
    (measurable_radialEnergy s hg k).comp measurable_subtype_coe
  have hA : Measurable (fun θ : sphere (0 : Mom d) 1 => ENNReal.ofReal (radialWeight d s k θ.1)) :=
    (measurable_radialWeight_unitSphere s k).ennreal_ofReal
  have hK : Measurable K := measurable_sphereSineInv.ennreal_ofReal
  have hU : Measurable U := ((hEf.comp measurable_fst).mul (hA.comp measurable_snd)).mul hK
  have hV : Measurable V := ((hEg.comp measurable_snd).mul (hA.comp measurable_fst)).mul hK
  have hUi : (∫⁻ p, U p ∂μ) ≤
      ENNReal.ofReal C * ENNReal.ofReal ((weightedL2Norm s f) ^ 2) := by
    simpa only [U, K, μ, ν, mul_assoc] using hb f hf hLf k
  have hVi : (∫⁻ p, V p ∂μ) ≤
      ENNReal.ofReal C * ENNReal.ofReal ((weightedL2Norm s g) ^ 2) := by
    have heq (p : sphere (0 : Mom d) 1 × sphere (0 : Mom d) 1) :
        V p = radialEnergy s g k p.2.1 * ENNReal.ofReal (radialWeight d s k p.1.1) *
          ENNReal.ofReal (angularSineInv p.2.1 p.1.1) := by
      dsimp only [V, K]
      rw [angularSineInv_symm (mem_sphere_zero_iff_norm.mp p.1.2)
        (mem_sphere_zero_iff_norm.mp p.2.2)]
    simp_rw [heq]
    have hswap : (∫⁻ p : sphere (0 : Mom d) 1 × sphere (0 : Mom d) 1,
        radialEnergy s g k p.2.1 * ENNReal.ofReal (radialWeight d s k p.1.1) *
          ENNReal.ofReal (angularSineInv p.2.1 p.1.1) ∂μ) =
        ∫⁻ p : sphere (0 : Mom d) 1 × sphere (0 : Mom d) 1,
          radialEnergy s g k p.1.1 * ENNReal.ofReal (radialWeight d s k p.2.1) *
            ENNReal.ofReal (angularSineInv p.1.1 p.2.1) ∂μ := by
      simpa only [Prod.swap, μ] using lintegral_prod_swap (μ := ν) (ν := ν)
        (fun p : sphere (0 : Mom d) 1 × sphere (0 : Mom d) 1 =>
          radialEnergy s g k p.1.1 * ENNReal.ofReal (radialWeight d s k p.2.1) *
            ENNReal.ofReal (angularSineInv p.1.1 p.2.1))
    rw [hswap]
    simpa only [mul_assoc] using hb g hg hLg k
  have hpoint (p : sphere (0 : Mom d) 1 × sphere (0 : Mom d) 1) :
      radialMass f k p.1.1 * radialMass g k p.2.1 * K p ≤
        U p ^ ((1 : ℝ) / 2) * V p ^ ((1 : ℝ) / 2) := by
    have h := mul_le_mul' (mul_le_mul'
      (radialMass_le_energy_weight hd s hs hf k p.1.1 (mem_sphere_zero_iff_norm.mp p.1.2))
      (radialMass_le_energy_weight hd s hs hg k p.2.1 (mem_sphere_zero_iff_norm.mp p.2.2)))
        (le_refl (K p))
    simpa only [ennreal_schur_pairing_kernel, U, V] using h
  have hconj : (2 : ℝ).HolderConjugate 2 := by rw [Real.holderConjugate_iff]; norm_num
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj
    (hU.pow_const ((1 : ℝ) / 2)).aemeasurable (hV.pow_const ((1 : ℝ) / 2)).aemeasurable
  simp only [ennreal_half_sq] at hHolder
  calc
    _ ≤ _ := lintegral_mono hpoint
    _ ≤ _ := hHolder
    _ ≤ (ENNReal.ofReal C * ENNReal.ofReal ((weightedL2Norm s f) ^ 2)) ^ ((1 : ℝ) / 2) *
        (ENNReal.ofReal C * ENNReal.ofReal ((weightedL2Norm s g) ^ 2)) ^ ((1 : ℝ) / 2) :=
      mul_le_mul' (ENNReal.rpow_le_rpow hUi (by norm_num))
        (ENNReal.rpow_le_rpow hVi (by norm_num))
    _ = _ := ennreal_schur_norm_constant _ _ _ (weightedL2Norm_nonneg _ _) (weightedL2Norm_nonneg _ _)

end WaveTurbulence.WKEL2
