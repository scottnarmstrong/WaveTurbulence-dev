/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.TensorFourier
public import WaveTurbulence.Foundations.RegAsymp.FrequencyShiftMoment
public import WaveTurbulence.Foundations.RegAsymp.FrequencyArrayNorm

/-! # The actual NT Fourier budget of a modulated product amplitude -/

public section
namespace WaveTurbulence.RegAsymp
open MeasureTheory
open scoped ENNReal FourierTransform

/-- Independent smooth cells, with arbitrary actual modulations, require
only one sum-frequency moment. This estimate is linear in that moment. -/
theorem fourierW_modulated_tensor_budget {d n : ℕ}
    (f g : Fin n → EuclideanSpace ℝ (Fin d) → ℂ)
    (hf : ∀ j, Measurable (𝓕 (f j))) (hg : ∀ j, Measurable (𝓕 (g j)))
    (β γ : Fin n → EuclideanSpace ℝ (Fin d)) :
    (∫⁻ τ : (Fin n → EuclideanSpace ℝ (Fin d)) × (Fin n → EuclideanSpace ℝ (Fin d)),
      ‖ApproxNT.fourierW (fun x y =>
        (∏ j, Real.fourierChar (inner ℝ (β j) (x j)) • f j (x j)) *
          (∏ j, Real.fourierChar (inner ℝ (γ j) (y j)) • g j (y j))) τ.1 τ.2‖ₑ *
        ENNReal.ofReal (1+2*Real.pi*ApproxNT.freqNorm τ.1 τ.2)) ≤
      ENNReal.ofReal (1+2*Real.pi) *
        (ENNReal.ofReal (1+((∑ j, ‖β j‖)+(∑ j, ‖γ j‖))) *
          ((∏ j, ∫⁻ ξ : EuclideanSpace ℝ (Fin d), ENNReal.ofReal (1+‖ξ‖)*‖𝓕 (f j) ξ‖ₑ) *
            (∏ j, ∫⁻ ξ : EuclideanSpace ℝ (Fin d), ENNReal.ofReal (1+‖ξ‖)*‖𝓕 (g j) ξ‖ₑ))) := by
  have hFourier (ξ η : Fin n → EuclideanSpace ℝ (Fin d)) :
      ApproxNT.fourierW (fun x y =>
        (∏ j, Real.fourierChar (inner ℝ (β j) (x j)) • f j (x j)) *
          (∏ j, Real.fourierChar (inner ℝ (γ j) (y j)) • g j (y j))) ξ η =
        (∏ j, 𝓕 (f j) (ξ j-β j))*(∏ j, 𝓕 (g j) (η j-γ j)) := by
    rw [fourierW_tensor_factorization
      (fun j x => Real.fourierChar (inner ℝ (β j) x) • f j x)
      (fun j y => Real.fourierChar (inner ℝ (γ j) y) • g j y) ξ η]
    simp only [fourier_positive_modulation]
  calc
    _ ≤ ∫⁻ τ : (Fin n → EuclideanSpace ℝ (Fin d)) × (Fin n → EuclideanSpace ℝ (Fin d)),
        ENNReal.ofReal (1+2*Real.pi) *
          (ENNReal.ofReal (1+((∑ j, ‖τ.1 j‖)+(∑ j, ‖τ.2 j‖))) *
            ((∏ j, ‖𝓕 (f j) (τ.1 j-β j)‖ₑ)*(∏ j, ‖𝓕 (g j) (τ.2 j-γ j)‖ₑ))) := by
      apply lintegral_mono
      intro τ
      dsimp only
      have hfreq := freqNorm_le_sum τ.1 τ.2
      rw [Finset.sum_add_distrib] at hfreq
      have hsum : 0 ≤ (∑ j, ‖τ.1 j‖)+(∑ j, ‖τ.2 j‖) := by positivity
      have hwt : 1+2*Real.pi*ApproxNT.freqNorm τ.1 τ.2 ≤
          (1+2*Real.pi)*(1+((∑ j, ‖τ.1 j‖)+(∑ j, ‖τ.2 j‖))) := by
        have hh := mul_le_mul_of_nonneg_left hfreq (by positivity : 0 ≤ 2*Real.pi)
        nlinarith [Real.pi_pos]
      have hh := ENNReal.ofReal_le_ofReal hwt
      rw [ENNReal.ofReal_mul (by positivity)] at hh
      rw [hFourier,enorm_mul,ApproxNT.enorm_finset_prod,ApproxNT.enorm_finset_prod]
      simpa only [mul_assoc,mul_left_comm,mul_comm] using mul_le_mul' (le_refl
        ((∏ j, ‖𝓕 (f j) (τ.1 j-β j)‖ₑ)*(∏ j, ‖𝓕 (g j) (τ.2 j-γ j)‖ₑ))) hh
    _ = ENNReal.ofReal (1+2*Real.pi) *
        (∫⁻ τ : (Fin n → EuclideanSpace ℝ (Fin d)) × (Fin n → EuclideanSpace ℝ (Fin d)),
          ENNReal.ofReal (1+((∑ j, ‖τ.1 j‖)+(∑ j, ‖τ.2 j‖))) *
            ((∏ j, ‖𝓕 (f j) (τ.1 j-β j)‖ₑ)*(∏ j, ‖𝓕 (g j) (τ.2 j-γ j)‖ₑ))) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ _ := mul_le_mul' le_rfl (lintegral_shifted_pair_frequency_moment_le β γ
      (fun j ξ => ‖𝓕 (f j) ξ‖ₑ) (fun j ξ => ‖𝓕 (g j) ξ‖ₑ)
      (fun j => (hf j).enorm) (fun j => (hg j).enorm))

end WaveTurbulence.RegAsymp
