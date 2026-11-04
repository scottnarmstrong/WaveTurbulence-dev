/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.SelectedDensityBound

/-!
# The actual root-density endpoint bounds

TARGET (incohproof18): one dimensional constant controls the L¹ norm
and the pointwise bound with the additional factor `L^(2d)`. The source
time-order domain is retained literally throughout the construction.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- TARGET (incohproof18), both actual endpoint estimates with one common base constant. -/
theorem exists_rootDensity_endpoint_bounds (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
        ∀ R : RootCoordinates n,
        (eLpNorm (R.linkDensity L γ δ Q I) 1 ≤
          ENNReal.ofReal ((C₀ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q))) ∧
        (∀ t, ‖R.linkDensity L γ δ Q I t‖ₑ ≤
          ENNReal.ofReal ((C₀ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q)) *
            ENNReal.ofReal (L ^ (2 * (d : ℝ)))) := by
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_rootDensity_L1_bound d hd
  obtain ⟨C₂, hC₂, hb₂⟩ := exists_selectedDensity_bound d hd
  let C₀ := C₁ + C₂
  have hC₀ : 0 < C₀ := add_pos hC₁ hC₂
  have hC₁₀ : C₁ ≤ C₀ := by dsimp [C₀]; linarith
  have hC₂₀ : C₂ ≤ C₀ := by dsimp [C₀]; linarith
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ η hη hηg δ hδ hδ₁ D hD
  obtain ⟨L₁, hL₁, hb₁⟩ := hb₁ γ hγ η hη hηg δ hδ D hD
  obtain ⟨L₂, hL₂, hb₂⟩ := hb₂ γ hγ η hη hηg δ hδ hδ₁ D hD
  refine ⟨max L₁ L₂, hL₁.trans (le_max_left _ _), ?_⟩
  intro L hL n Q hspan I hI hbox R
  have hLa := (le_max_left L₁ L₂).trans hL
  have hLb := (le_max_right L₁ L₂).trans hL
  have hLp := zero_lt_one.trans_le (hL₁.trans hLa)
  have hpow₁ : (C₁ * δ) ^ n ≤ (C₀ * δ) ^ n :=
    pow_le_pow_left₀ (mul_nonneg hC₁.le hδ.le) (mul_le_mul_of_nonneg_right hC₁₀ hδ.le) n
  have hpow₂ : (C₂ * δ) ^ n ≤ (C₀ * δ) ^ n :=
    pow_le_pow_left₀ (mul_nonneg hC₂.le hδ.le) (mul_le_mul_of_nonneg_right hC₂₀ hδ.le) n
  have hA : 0 ≤ (C₀ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q) := by positivity
  constructor
  · exact (hb₁ L hLa n Q hspan I hI hbox R).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hpow₁ (Real.rpow_nonneg hLp.le _)))
  · intro t
    rw [← ENNReal.ofReal_mul hA]
    have hpoint := hb₂ L hLb n Q hspan I hbox 2 R t
    norm_num only [Nat.cast_ofNat] at hpoint
    rw [mul_comm (d : ℝ) 2] at hpoint
    exact hpoint.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpow₂ (Real.rpow_nonneg hLp.le _)) (Real.rpow_nonneg hLp.le _)))

end WaveTurbulence.Incoh
