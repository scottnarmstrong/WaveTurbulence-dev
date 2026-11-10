/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.ShiftedGevreyEnvelope
public import WaveTurbulence.Foundations.RegAsymp.CoefficientEnvelopeData

/-! # The literal source coefficient envelope after a fixed derivative shift -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR
open scoped ENNReal

/-- Shift the source derivative order while retaining the NT denominator. -/
def shiftedDerivativeCoefficientEnvelope {ι : Type} [Fintype ι] (s : ℕ)
    (C : (ι → ℝ) → ℝ × ℝ → ℂ) (lam : ℝ × ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal (1/((4*k).factorial:ℝ))*∫⁻ α, dnorm (k+s) C α lam

theorem measurable_shiftedDerivativeCoefficientEnvelope {ι : Type} [Fintype ι]
    (s : ℕ) {C : (ι → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C) :
    Measurable (shiftedDerivativeCoefficientEnvelope s C) := by
  apply Measurable.tsum
  intro k
  exact ((measurable_dnorm hC.smooth hC.meas (k+s)).lintegral_prod_left').const_mul _

/-- The shifted common envelope retains the original strong temporal weight. -/
theorem shiftedDerivativeCoefficientEnvelope_mass_le {ι : Type} [Fintype ι]
    (s : ℕ) {C : (ι → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C) {θ N A : ℝ} (hN : 0 ≤ N)
    (hmain : ∀ k, ∫⁻ α, ∫⁻ lam, wL θ lam*dnorm k C α lam ≤ gev N A k) :
    (∫⁻ lam, wL θ lam*shiftedDerivativeCoefficientEnvelope s C lam) ≤
      ENNReal.ofReal N*∑' k : ℕ, ENNReal.ofReal (A^(k+s)*((2*(k+s)).factorial:ℝ)/(4*k).factorial) := by
  let G := fun k lam => ∫⁻ α, wL θ lam*dnorm (k+s) C α lam
  have hm (k : ℕ) : Measurable (fun p : (ι → ℝ) × (ℝ × ℝ) =>
      wL θ p.2*dnorm (k+s) C p.1 p.2) :=
    ((measurable_wL θ).comp measurable_snd).mul (measurable_dnorm hC.smooth hC.meas (k+s))
  have hG (k : ℕ) : Measurable (G k) := (hm k).lintegral_prod_left'
  have he (lam : ℝ × ℝ) : wL θ lam*shiftedDerivativeCoefficientEnvelope s C lam =
      ∑' k : ℕ, ENNReal.ofReal (1/((4*k).factorial:ℝ))*G k lam := by
    unfold shiftedDerivativeCoefficientEnvelope
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro k
    dsimp only [G]
    rw [lintegral_const_mul _ (measurable_dnorm hC.smooth hC.meas (k+s)).of_uncurry_right]
    exact mul_left_comm _ _ _
  simp_rw [he]
  apply lintegral_shifted_gevrey_envelope_le s G hG hN
  intro k
  change (∫⁻ lam, ∫⁻ α, wL θ lam*dnorm (k+s) C α lam) ≤ _
  rw [← lintegral_lintegral_swap (hm k).aemeasurable]
  exact hmain (k+s)

end WaveTurbulence.RegAsymp
