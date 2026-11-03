/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.LossOneInfrastructure
public import WaveTurbulence.Foundations.WKEL2.PairSliceBound

/-!
# Weighted squared spherical-average bound

Research-note Proposition 6, the estimate of N² before the last spatial
Cauchy–Schwarz inequality. The delta normalization one half is kept outside.
-/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped InnerProductSpace ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- The squared spherical average is controlled by the exact frozen weighted energy. -/
theorem exists_sphericalLossAverage_square_bound (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : Mom d → ℝ, Measurable h →
      MemLp (weightedFunction s h) 2 → ∀ k : Mom d,
      (∫⁻ w : Mom d, ENNReal.ofReal (japaneseDecay (2 * s) (k + w)) *
        (sphericalLossAverage h k w) ^ 2) ≤
        ENNReal.ofReal C * ENNReal.ofReal ((weightedL2Norm s h) ^ 2) := by
  obtain ⟨C, hC, hb⟩ := exists_sine_mass_bound hd s hs
  refine ⟨transverseDecayMass d s * C, mul_nonneg (transverseDecayMass_nonneg _ _) hC,
    fun h hh hLh k => ?_⟩
  let ν := (volume : Measure (Mom d)).toSphere
  let H : Mom d × sphere (0 : Mom d) 1 → ℝ≥0∞ := fun p =>
    raySample h k p.2.1 ⟪(p.2.1 : Mom d), p.1⟫_ℝ
  let W : Mom d → ℝ≥0∞ := fun w => ENNReal.ofReal (japaneseDecay (2 * s) (k + w))
  have hH : Measurable H := measurable_sphericalLossIntegrand hh k
  have hW : Measurable W := by
    have hc : Continuous (fun w : Mom d => 1 + ‖k + w‖ ^ 2) := by fun_prop
    exact (hc.rpow_const (fun _ => Or.inl (by positivity))).measurable.ennreal_ofReal
  let J : (sphere (0 : Mom d) 1 × sphere (0 : Mom d) 1) × Mom d → ℝ≥0∞ :=
    fun p => W p.2 * H (p.2, p.1.1) * H (p.2, p.1.2)
  have hJ : Measurable J :=
    ((hW.comp measurable_snd).mul
      (hH.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst)))).mul
        (hH.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  let B : sphere (0 : Mom d) 1 × sphere (0 : Mom d) 1 → ℝ≥0∞ := fun p =>
    radialMass h k p.1.1 * radialMass h k p.2.1 * ENNReal.ofReal (angularSineInv p.1.1 p.2.1)
  have hMass : Measurable (fun θ : sphere (0 : Mom d) 1 => radialMass h k θ.1) :=
    (measurable_radialMass hh k).comp measurable_subtype_coe
  have hB : Measurable B :=
    ((hMass.comp measurable_fst).mul (hMass.comp measurable_snd)).mul
      measurable_sphereSineInv.ennreal_ofReal
  have hpoint (θ : sphere (0 : Mom d) 1) :
      ∀ᵐ v : sphere (0 : Mom d) 1 ∂ν,
        (∫⁻ w : Mom d, J ((θ, v), w)) ≤ ENNReal.ofReal (transverseDecayMass d s) * B (θ, v) := by
    have hθ : ‖(θ : Mom d)‖ = 1 := mem_sphere_zero_iff_norm.mp θ.2
    have hθ0 : (θ : Mom d) ≠ 0 := by intro h0; simp only [h0, norm_zero, zero_ne_one] at hθ
    filter_upwards [ae_transverseAxis_ne_zero (by omega : 2 ≤ d) hθ0] with v hv
    have he := lintegral_pair_slice_le hd s hs hθ hθ0 hv
      (measurable_raySample hh k θ.1) (measurable_raySample hh k v.1) k
    rw [lintegral_raySample hh k θ.1, lintegral_raySample hh k v.1] at he
    have he' : (∫⁻ w : Mom d, J ((θ, v), w)) ≤
        ENNReal.ofReal (transverseDecayMass d s) * ENNReal.ofReal (angularSineInv θ.1 v.1) *
          radialMass h k θ.1 * radialMass h k v.1 := he
    exact he'.trans_eq (by dsimp only [B]; ac_rfl)
  have hSq := lintegral_weighted_square volume ν hW hH
  have hMean : Measurable (fun p : sphere (0 : Mom d) 1 × sphere (0 : Mom d) 1 =>
      ∫⁻ w : Mom d, J (p, w)) := hJ.lintegral_prod_right'
  calc
    _ = ∫⁻ p : sphere (0 : Mom d) 1 × sphere (0 : Mom d) 1,
        ∫⁻ w : Mom d, J (p, w) ∂volume ∂ν.prod ν := hSq
    _ = ∫⁻ θ : sphere (0 : Mom d) 1, ∫⁻ v : sphere (0 : Mom d) 1,
        ∫⁻ w : Mom d, J ((θ, v), w) ∂volume ∂ν ∂ν := lintegral_prod _ hMean.aemeasurable
    _ ≤ ∫⁻ θ : sphere (0 : Mom d) 1, ∫⁻ v : sphere (0 : Mom d) 1,
        ENNReal.ofReal (transverseDecayMass d s) * B (θ, v) ∂ν ∂ν :=
      lintegral_mono fun θ => lintegral_mono_ae (hpoint θ)
    _ = ∫⁻ p, ENNReal.ofReal (transverseDecayMass d s) * B p ∂ν.prod ν :=
      (lintegral_prod _ (measurable_const.mul hB).aemeasurable).symm
    _ = ENNReal.ofReal (transverseDecayMass d s) * ∫⁻ p, B p ∂ν.prod ν :=
      lintegral_const_mul _ hB
    _ ≤ ENNReal.ofReal (transverseDecayMass d s) *
        (ENNReal.ofReal C * ENNReal.ofReal ((weightedL2Norm s h) ^ 2)) := by
      have hbound := hb h h hh hh hLh hLh k
      rw [← pow_two] at hbound
      exact mul_le_mul' le_rfl hbound
    _ = _ := by rw [ENNReal.ofReal_mul (transverseDecayMass_nonneg _ _), mul_assoc]

end WaveTurbulence.WKEL2
