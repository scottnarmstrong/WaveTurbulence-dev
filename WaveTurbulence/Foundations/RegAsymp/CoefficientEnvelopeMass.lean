/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.CoefficientEnvelopeData

/-! # Quantitative weighted masses of the actual J3 symbol envelopes -/

public section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR
open scoped ENNReal
variable {ι : Type} [Fintype ι]

/-- Changing to a weaker temporal weight costs no frequency factor. -/
theorem temporalWeight_mono {a θ : ℝ} (haθ : a ≤ θ) (lam : ℝ × ℝ) : wL a lam ≤ wL θ lam := by
  unfold wL
  apply ENNReal.rpow_le_rpow_of_exponent_le _ haθ
  exact (le_self_add : (1:ℝ≥0∞) ≤ 1+‖lam.1‖ₑ).trans le_self_add

/-- The explicit common derivative envelope has exactly the J3 Gevrey mass. -/
theorem derivativeCoefficientEnvelope_mass_le {C : (ι → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C)
    {θ N A : ℝ} (hN : 0 ≤ N)
    (hmain : ∀ k, ∫⁻ α, ∫⁻ lam, wL θ lam*dnorm k C α lam ≤ gev N A k) :
    (∫⁻ lam, wL θ lam*derivativeCoefficientEnvelope C lam) ≤
      ENNReal.ofReal N * ∑' k : ℕ, ENNReal.ofReal (A^k*((2*k).factorial:ℝ)/(4*k).factorial) := by
  simp_rw [wL_mul_derivativeCoefficientEnvelope θ hC]
  exact coefficient_derivative_envelope_le hC hN hmain

/-- The explicit moment envelope has only the cardinality loss from the
literal per-variable J3 field. No maximum-measurability premise is needed. -/
theorem momentCoefficientEnvelope_mass_le {C : (ι → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C)
    {a b N : ℝ}
    (hper : ∀ i : ι, ∫⁻ α, ∫⁻ lam, wL a lam*(1+‖α i‖ₑ)^b*‖C α lam‖ₑ ≤ ENNReal.ofReal N) :
    (∫⁻ lam, wL a lam*momentCoefficientEnvelope b C lam) ≤
      Fintype.card ι * ENNReal.ofReal N := by
  classical
  let B : ι → (ι → ℝ) → (ℝ × ℝ) → ℝ≥0∞ := fun i α lam => (1+‖α i‖ₑ)^b*‖C α lam‖ₑ
  have hm (i : ι) : Measurable (Function.uncurry (B i)) :=
    (by fun_prop : Measurable (fun p : (ι → ℝ) × (ℝ × ℝ) => (1+‖p.1 i‖ₑ)^b)).mul
      hC.meas.measurable.enorm
  have hwm (i : ι) : Measurable (fun p : (ι → ℝ) × (ℝ × ℝ) => wL a p.2*B i p.1 p.2) :=
    ((measurable_wL a).comp measurable_snd).mul (hm i)
  have hterm (i : ι) : (∫⁻ lam, wL a lam*∫⁻ α, B i α lam) ≤ ENNReal.ofReal N := by
    calc
      _ = ∫⁻ lam, ∫⁻ α, wL a lam*B i α lam := by
        apply lintegral_congr
        intro lam
        exact (lintegral_const_mul _ (hm i).of_uncurry_right).symm
      _ = ∫⁻ α, ∫⁻ lam, wL a lam*B i α lam := (lintegral_lintegral_swap (hwm i).aemeasurable).symm
      _ ≤ _ := by simpa only [B,mul_assoc] using hper i
  unfold momentCoefficientEnvelope
  change (∫⁻ lam, wL a lam*∑ i, ∫⁻ α, B i α lam) ≤ _
  simp_rw [Finset.mul_sum]
  rw [lintegral_finsetSum (f := fun i lam => wL a lam*(∫⁻ α, B i α lam)) _ (fun i _ => (measurable_wL a).mul ((hm i).lintegral_prod_left'))]
  calc
    _ ≤ ∑ _i : ι, ENNReal.ofReal N := Finset.sum_le_sum (fun i _ => hterm i)
    _ = _ := by simp

/-- Both actual NT symbol budgets share one quantitative frequency envelope. -/
theorem combinedCoefficientEnvelope_mass_le {C : (ι → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C)
    {a θ b N A : ℝ} (haθ : a ≤ θ) (hN : 0 ≤ N)
    (hmain : ∀ k, ∫⁻ α, ∫⁻ lam, wL θ lam*dnorm k C α lam ≤ gev N A k)
    (hper : ∀ i : ι, ∫⁻ α, ∫⁻ lam, wL a lam*(1+‖α i‖ₑ)^b*‖C α lam‖ₑ ≤ ENNReal.ofReal N) :
    (∫⁻ lam, wL a lam*(derivativeCoefficientEnvelope C lam+momentCoefficientEnvelope b C lam)) ≤
      ENNReal.ofReal N*(∑' k : ℕ, ENNReal.ofReal (A^k*((2*k).factorial:ℝ)/(4*k).factorial)) +
        Fintype.card ι*ENNReal.ofReal N := by
  simp_rw [mul_add]
  rw [lintegral_add_left (f := fun lam => wL a lam*derivativeCoefficientEnvelope C lam)
    ((measurable_wL a).mul (measurable_derivativeCoefficientEnvelope hC))
    (fun lam => wL a lam*momentCoefficientEnvelope b C lam)]
  apply add_le_add _ (momentCoefficientEnvelope_mass_le hC hper)
  exact (lintegral_mono (fun lam => mul_le_mul' (temporalWeight_mono haθ lam) le_rfl)).trans
    (derivativeCoefficientEnvelope_mass_le hC hN hmain)

end WaveTurbulence.RegAsymp
