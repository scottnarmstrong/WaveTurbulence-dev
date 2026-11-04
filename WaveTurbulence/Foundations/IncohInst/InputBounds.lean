/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.Regref.Inputs
public import WaveTurbulence.Foundations.WaveB.FrozenB2

/-! # Uniform original source inputs in the exact B2 parameter prefix -/

public section
noncomputable section
open MeasureTheory Set
namespace WaveTurbulence.IncohInst

/-- The actual B2 inputs have a bound depending only on the Schwartz solution. -/
theorem inputsF_spatialNorm_le (P : WTParams) (hd : 1 ≤ P.d)
    (hL : 1 ≤ P.L) (hδ : 0 ≤ P.δ) (hT : P.τstar = P.D * P.δ)
    {B : ℝ} (hB : 0 ≤ B)
    (hφ : ∀ τ ∈ Icc 0 P.τstar, SNormR (40 * P.d) (40 * P.d) (P.φ τ) ≤ ENNReal.ofReal B)
    {p : ℕ} (hp : p ≤ P.D) (R : ℕ → Mom P.d → ℝ)
    (hR : ∀ q ≤ p, InputRemainder P (R q) q) :
    ∀ r ≤ p, Fourier.spatialNorm (40 * P.d) (40 * P.d)
      (fun k => (inputsF P R r k : ℂ)) ≤ ENNReal.ofReal (B + 1) := by
  intro r hr
  rw [← NormBridgeScratch.SNormR_eq_spatialNorm]
  change SNormR (40 * P.d) (40 * P.d) (fun k => P.φ (P.δ * r) k + R r k) ≤ _
  apply Regref.SNormR_input_le (by omega) _ hB zero_le_one
  · apply hφ
    constructor
    · exact mul_nonneg hδ (Nat.cast_nonneg _)
    · rw [hT, mul_comm (P.D : ℝ)]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hr.trans hp) hδ
  · apply (hR r hr).trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_one_of_one_le_of_nonpos hL
    have hθ : 0 ≤ P.theta r := by unfold WTParams.theta; positivity
    exact neg_nonpos.mpr hθ

end WaveTurbulence.IncohInst
