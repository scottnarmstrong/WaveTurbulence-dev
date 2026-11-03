/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.M1
public import WaveTurbulence.Foundations.WKEL2.SineKernel
public import WaveTurbulence.Foundations.WKEL2.AngularSchur

/-!
# The angular Schur energy bound with the sine denominator

Research-note Proposition 6 uses Lemma 4(b) on the full sphere.
-/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Nonnegative integral version of the uniform M₁ estimate. -/
theorem exists_sphere_M1_lintegral (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : sphere (0 : Mom d) 1, ∀ k : Mom d,
      (∫⁻ v : sphere (0 : Mom d) 1,
        ENNReal.ofReal (radialWeight d s k v.1) * ENNReal.ofReal (angularSineInv θ.1 v.1)
          ∂(volume : Measure (Mom d)).toSphere) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_M1 hd s hs
  refine ⟨C, hC, fun θ k => ?_⟩
  have hθ : (θ : Mom d) ≠ 0 := by
    intro h
    have hn := mem_sphere_zero_iff_norm.mp θ.2
    simp only [h, norm_zero, zero_ne_one] at hn
  obtain ⟨hi, hb⟩ := hb θ.1 hθ k
  have hn : 0 ≤ᵐ[(volume : Measure (Mom d)).toSphere]
      (fun v : sphere (0 : Mom d) 1 => radialWeight d s k v.1 * angularSineInv θ.1 v.1) :=
    Filter.Eventually.of_forall fun v =>
      mul_nonneg (radialWeight_nonneg _ _ _ _) (angularSineInv_nonneg _ _)
  simp_rw [← ENNReal.ofReal_mul (radialWeight_nonneg _ _ _ _)]
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn]
  exact ENNReal.ofReal_le_ofReal hb

/-- A ray energy paired with the opposite weighted sine kernel is uniformly bounded. -/
theorem exists_sine_schur_energy_bound (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Mom d → ℝ, Measurable f →
      MemLp (weightedFunction s f) 2 → ∀ k : Mom d,
      (∫⁻ p : sphere (0 : Mom d) 1 × sphere (0 : Mom d) 1,
        radialEnergy s f k p.1.1 * (ENNReal.ofReal (radialWeight d s k p.2.1) *
          ENNReal.ofReal (angularSineInv p.1.1 p.2.1))
          ∂((volume : Measure (Mom d)).toSphere.prod (volume : Measure (Mom d)).toSphere)) ≤
        ENNReal.ofReal C * ENNReal.ofReal ((weightedL2Norm s f) ^ 2) := by
  obtain ⟨C, hC, hb⟩ := exists_sphere_M1_lintegral hd s hs
  refine ⟨C, hC, fun f hf hLf k => ?_⟩
  have hE : Measurable (fun v : sphere (0 : Mom d) 1 => radialEnergy s f k v.1) :=
    (measurable_radialEnergy s hf k).comp measurable_subtype_coe
  have hA : Measurable (fun v : sphere (0 : Mom d) 1 => ENNReal.ofReal (radialWeight d s k v.1)) :=
    (measurable_radialWeight_unitSphere s k).ennreal_ofReal
  have hS := measurable_sphereSineInv (d := d) |>.ennreal_ofReal
  have hI : Measurable (fun p : sphere (0 : Mom d) 1 × sphere (0 : Mom d) 1 =>
      radialEnergy s f k p.1.1 * (ENNReal.ofReal (radialWeight d s k p.2.1) *
        ENNReal.ofReal (angularSineInv p.1.1 p.2.1))) :=
    (hE.comp measurable_fst).mul ((hA.comp measurable_snd).mul hS)
  rw [lintegral_prod _ hI.aemeasurable]
  calc
    _ ≤ ∫⁻ θ : sphere (0 : Mom d) 1, radialEnergy s f k θ.1 * ENNReal.ofReal C
        ∂(volume : Measure (Mom d)).toSphere := by
      apply lintegral_mono
      intro θ
      dsimp only
      have hm : Measurable (fun v : sphere (0 : Mom d) 1 =>
          ENNReal.ofReal (radialWeight d s k v.1) * ENNReal.ofReal (angularSineInv θ.1 v.1)) :=
        hA.mul ((measurable_angularSineInv θ.1).comp measurable_subtype_coe).ennreal_ofReal
      rw [lintegral_const_mul _ hm]
      exact mul_le_mul' le_rfl (hb θ k)
    _ = _ := by
      rw [lintegral_mul_const _ hE, lintegral_radialEnergy (by omega) s hf hLf k, mul_comm]

end WaveTurbulence.WKEL2
