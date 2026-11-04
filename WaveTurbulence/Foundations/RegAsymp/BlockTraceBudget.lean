/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.BlockTraceEnvelope
public import WaveTurbulence.Foundations.RegAsymp.UniformShiftedGevrey

/-! # Quantitative source masses for a growing block of Wick energy traces -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR
open scoped ENNReal

/-- Integrated form of the actual block-envelope inequality. -/
theorem derivativeCoefficientEnvelope_blockTrace_mass_le_sum {r : ℕ} {κ : Type} [Fintype κ]
    {C : (Fin r ⊕ κ → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C) (θ : ℝ) :
    (∫⁻ lam, wL θ lam*derivativeCoefficientEnvelope (blockTraceSymbol C) lam) ≤ (2:ℝ≥0∞)^r *
      ∑ j ∈ Finset.range (r+1), ENNReal.ofReal ((r:ℝ)^j)*
        ∫⁻ lam, wL θ lam*shiftedDerivativeCoefficientEnvelope j C lam := by
  apply le_trans (lintegral_mono (fun lam => mul_le_mul' le_rfl
    (derivativeCoefficientEnvelope_blockTrace_le hC lam)))
  have he (lam : ℝ × ℝ) : wL θ lam*((2:ℝ≥0∞)^r *
      ∑ j ∈ Finset.range (r+1), ENNReal.ofReal ((r:ℝ)^j)*shiftedDerivativeCoefficientEnvelope j C lam) =
      (2:ℝ≥0∞)^r * ∑ j ∈ Finset.range (r+1), ENNReal.ofReal ((r:ℝ)^j)*
        (wL θ lam*shiftedDerivativeCoefficientEnvelope j C lam) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ac_rfl
  simp_rw [he]
  rw [lintegral_const_mul' _ _ (by finiteness),lintegral_finsetSum (f := fun j lam =>
    ENNReal.ofReal ((r:ℝ)^j)*(wL θ lam*shiftedDerivativeCoefficientEnvelope j C lam)) _
      (fun j _ => measurable_const.mul ((measurable_wL θ).mul
        (measurable_shiftedDerivativeCoefficientEnvelope j hC)))]
  apply le_of_eq
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Literal J3 quantitative mass with finitely many derivative shifts. -/
theorem derivativeCoefficientEnvelope_blockTrace_mass_le {r : ℕ} {κ : Type} [Fintype κ]
    {C : (Fin r ⊕ κ → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C) {θ N A : ℝ} (hN : 0 ≤ N)
    (hmain : ∀ k, ∫⁻ α, ∫⁻ lam, wL θ lam*dnorm k C α lam ≤ gev N A k) :
    (∫⁻ lam, wL θ lam*derivativeCoefficientEnvelope (blockTraceSymbol C) lam) ≤ (2:ℝ≥0∞)^r *
      ∑ j ∈ Finset.range (r+1), ENNReal.ofReal ((r:ℝ)^j)*
        (ENNReal.ofReal N*∑' k : ℕ, ENNReal.ofReal (A^(k+j)*((2*(k+j)).factorial:ℝ)/(4*k).factorial)) := by
  apply (derivativeCoefficientEnvelope_blockTrace_mass_le_sum hC θ).trans
  apply mul_le_mul' le_rfl
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul' le_rfl (shiftedDerivativeCoefficientEnvelope_mass_le j hC hN hmain)

end WaveTurbulence.RegAsymp
