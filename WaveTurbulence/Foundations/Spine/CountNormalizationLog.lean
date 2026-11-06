/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CountANormalization
/-! Exact logarithm of the source countA normalization, including the integer circuit rank. -/
public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.LGSpine

theorem log_molecularCountNormalization {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) (d : ℕ) {L δ C₁ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hC₁ : 0 < C₁)
    (γ : ℝ) :
    Real.log (molecularCountNormalization M d L γ δ C₁) =
      (M.circuitRank : ℝ) * (-((d : ℝ) - γ) * Real.log L - Real.log C₁ + Real.log δ / 2) := by
  unfold molecularCountNormalization
  rw [Real.log_mul (Real.rpow_pos_of_pos hL _).ne'
    (zpow_pos (mul_pos (inv_pos.mpr hC₁) (Real.rpow_pos_of_pos hδ _)) _).ne',
    Real.log_rpow hL, Real.log_zpow,
    Real.log_mul (inv_pos.mpr hC₁).ne' (Real.rpow_pos_of_pos hδ _).ne',
    Real.log_inv, Real.log_rpow hδ]
  ring

end WaveTurbulence.LGSpine
