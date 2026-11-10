/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.PrincipalValue
public import WaveTurbulence.Foundations.Resonant.BilinearFourierLimit

/-!
# Matching the energy and bilinear principal-value normalizations

The collision energy is `-2⟨ℓ,x⟩`; DH21 Lemma 6.3 uses `⟨ℓ,x⟩` on the square
torus. Evenness of the cutoff gives the exact factor `-1/2` and scale `2μ`.
-/

public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace NNReal ContDiff

namespace WaveTurbulence.Resonant

variable {d : ℕ}

/-- Exact normalization bridge at every finite scale, before taking principal values. -/
theorem energyInvIntegral_eq_bilinearFourierTruncation
    {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) (μ : ℝ) (F : Mom d → Mom d → ℝ) :
    (energyInvIntegral χ μ F : ℂ) = -(2 : ℂ)⁻¹ *
      bilinearFourierTruncation χ (2 * μ) (fun ℓ x => (F ℓ x : ℂ)) 0 0 := by
  have hq : ∀ r : ℝ, (1 - χ (μ * (-(2 * r)))) / (-(2 * r)) =
      -(2 : ℝ)⁻¹ * ((1 - χ ((2 * μ) * r)) / r) := by
    intro r
    rw [mul_neg, hχ.even]
    have he : μ * (2 * r) = (2 * μ) * r := by ring
    rw [he]
    simp only [div_eq_mul_inv, inv_neg, mul_inv]
    ring
  rw [energyInvIntegral, ← integral_complex_ofReal, bilinearFourierTruncation, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ℓ => ?_)
  simp only [inner_zero_left, unitPhase, one_mul, zero_mul, Complex.ofReal_zero, Complex.exp_zero]
  rw [energyInvInner, ← integral_complex_ofReal, bilinearInvFourierInner, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [inner_zero_left, unitPhase, one_mul, zero_mul, Complex.ofReal_zero, Complex.exp_zero,
    hq, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_inv, Complex.ofReal_ofNat]
  ring

end WaveTurbulence.Resonant
