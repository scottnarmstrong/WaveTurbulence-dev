/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.TraceDerivativeIntegral
public import WaveTurbulence.Foundations.RegAsymp.ShiftedCoefficientEnvelope

/-! # A finite common frequency envelope for the Wick coefficient trace -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR
open scoped ENNReal

/-- Every derivative of the trace is paid by two fixed-shift source envelopes. -/
theorem derivativeCoefficientEnvelope_trace_le {ι : Type} [Fintype ι]
    {C : (Option ι → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C) (lam : ℝ × ℝ) :
    derivativeCoefficientEnvelope (traceSymbol C) lam ≤
      shiftedDerivativeCoefficientEnvelope 0 C lam+shiftedDerivativeCoefficientEnvelope 1 C lam := by
  unfold derivativeCoefficientEnvelope shiftedDerivativeCoefficientEnvelope
  calc
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (1/((4*k).factorial:ℝ))*
        ((∫⁻ α, dnorm k C α lam)+(∫⁻ α, dnorm (k+1) C α lam)) :=
      ENNReal.tsum_le_tsum (fun k => mul_le_mul' le_rfl (lintegral_dnorm_traceSymbol_le (hC.smooth lam) k))
    _ = _ := by simp only [mul_add,ENNReal.tsum_add,Nat.add_zero]

/-- The one-coordinate trace retains finite mass under the original
strong temporal weight. No frequency-moment field is needed. -/
theorem derivativeCoefficientEnvelope_trace_mass_lt_top {ι : Type} [Fintype ι]
    {C : (Option ι → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C) {θ N A : ℝ}
    (hN : 0 ≤ N) (hA : 0 ≤ A)
    (hmain : ∀ k, ∫⁻ α, ∫⁻ lam, wL θ lam*dnorm k C α lam ≤ gev N A k) :
    (∫⁻ lam, wL θ lam*derivativeCoefficientEnvelope (traceSymbol C) lam) < ⊤ := by
  apply lt_of_le_of_lt (lintegral_mono (fun lam => mul_le_mul' le_rfl
    (derivativeCoefficientEnvelope_trace_le hC lam)))
  simp_rw [mul_add]
  rw [lintegral_add_left (f := fun lam => wL θ lam*shiftedDerivativeCoefficientEnvelope 0 C lam)
    ((measurable_wL θ).mul (measurable_shiftedDerivativeCoefficientEnvelope 0 hC))]
  exact ENNReal.add_lt_top.mpr ⟨shiftedDerivativeCoefficientEnvelope_mass_lt_top 0 hC hN hA hmain,
    shiftedDerivativeCoefficientEnvelope_mass_lt_top 1 hC hN hA hmain⟩

/-- Quantitative strong weighted trace mass, with exactly two fixed shifts. -/
theorem derivativeCoefficientEnvelope_trace_mass_le {ι : Type} [Fintype ι]
    {C : (Option ι → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C) {θ N A : ℝ} (hN : 0 ≤ N)
    (hmain : ∀ k, ∫⁻ α, ∫⁻ lam, wL θ lam*dnorm k C α lam ≤ gev N A k) :
    (∫⁻ lam, wL θ lam*derivativeCoefficientEnvelope (traceSymbol C) lam) ≤
      ENNReal.ofReal N*((∑' k : ℕ, ENNReal.ofReal (A^k*((2*k).factorial:ℝ)/(4*k).factorial))+
        (∑' k : ℕ, ENNReal.ofReal (A^(k+1)*((2*(k+1)).factorial:ℝ)/(4*k).factorial))) := by
  apply le_trans (lintegral_mono (fun lam => mul_le_mul' le_rfl
    (derivativeCoefficientEnvelope_trace_le hC lam)))
  simp_rw [mul_add]
  rw [lintegral_add_left (f := fun lam => wL θ lam*shiftedDerivativeCoefficientEnvelope 0 C lam)
    ((measurable_wL θ).mul (measurable_shiftedDerivativeCoefficientEnvelope 0 hC))]
  have hh := add_le_add (shiftedDerivativeCoefficientEnvelope_mass_le 0 hC hN hmain)
    (shiftedDerivativeCoefficientEnvelope_mass_le 1 hC hN hmain)
  simpa only [Nat.add_zero,mul_add] using hh

end WaveTurbulence.RegAsymp
