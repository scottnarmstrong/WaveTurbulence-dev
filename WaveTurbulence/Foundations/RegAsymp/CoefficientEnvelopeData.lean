/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.CoefficientEnvelope
public import WaveTurbulence.Foundations.RegAsymp.EnvelopePointwise
public import WaveTurbulence.Foundations.RegAsymp.MomentWeights
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! # Literal common scalar envelopes of the J3 coefficient symbol -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR
open scoped ENNReal
variable {ι : Type} [Fintype ι]

/-- A single unweighted derivative envelope, valid for all derivative words. -/
def derivativeCoefficientEnvelope (C : (ι → ℝ) → ℝ × ℝ → ℂ) (lam : ℝ × ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal (1/((4*k).factorial:ℝ)) * ∫⁻ α, dnorm k C α lam

/-- The literal per-variable J3 moment envelope. Summing over variables
costs only their cardinality, and includes the empty-variable case. -/
def momentCoefficientEnvelope (b : ℝ) (C : (ι → ℝ) → ℝ × ℝ → ℂ) (lam : ℝ × ℝ) : ℝ≥0∞ :=
  ∑ i, ∫⁻ α, (1+‖α i‖ₑ)^b * ‖C α lam‖ₑ

theorem measurable_derivativeCoefficientEnvelope {C : (ι → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C) :
    Measurable (derivativeCoefficientEnvelope C) := by
  apply Measurable.tsum
  intro k
  exact ((measurable_dnorm hC.smooth hC.meas k).lintegral_prod_left').const_mul _

theorem measurable_momentCoefficientEnvelope (b : ℝ) {C : (ι → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C) :
    Measurable (momentCoefficientEnvelope b C) := by
  apply Finset.measurable_sum
  intro i _
  have hm : Measurable (fun p : (ι → ℝ) × (ℝ × ℝ) => (1+‖p.1 i‖ₑ)^b * ‖C p.1 p.2‖ₑ) :=
    (by fun_prop : Measurable (fun p : (ι → ℝ) × (ℝ × ℝ) => (1+‖p.1 i‖ₑ)^b)).mul
      hC.meas.measurable.enorm
  exact hm.lintegral_prod_left'

/-- Every derivative order is controlled by the same scalar envelope. -/
theorem derivativeCoefficientEnvelope_dominates (C : (ι → ℝ) → ℝ × ℝ → ℂ) (k : ℕ) (lam : ℝ × ℝ) :
    (∫⁻ α, dnorm k C α lam) ≤
      ENNReal.ofReal ((4*k).factorial:ℝ) * derivativeCoefficientEnvelope C lam :=
  gevrey_envelope_dominates (fun k lam => ∫⁻ α, dnorm k C α lam) k lam

/-- The NT maximum moment is dominated pointwise in the temporal frequency. -/
theorem momentCoefficientEnvelope_dominates {b : ℝ} (hb : 0 ≤ b)
    {C : (ι → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C) (lam : ℝ × ℝ) :
    (∫⁻ α, ENNReal.ofReal (ApproxNT.wmax b α)*‖C α lam‖ₑ) ≤ momentCoefficientEnvelope b C lam := by
  classical
  calc
    _ ≤ ∫⁻ α, ∑ i, (1+‖α i‖ₑ)^b*‖C α lam‖ₑ := by
      apply lintegral_mono
      intro α
      simpa only [Finset.sum_mul] using mul_le_mul' (ofReal_wmax_le_sum hb α) (le_refl ‖C α lam‖ₑ)
    _ = _ := by
      apply lintegral_finsetSum
      intro i _
      exact (by fun_prop : Measurable (fun α : ι → ℝ => (1+‖α i‖ₑ)^b)).mul
        (hC.meas.measurable.of_uncurry_right.enorm)

/-- Pull the literal temporal weight through the common derivative envelope. -/
theorem wL_mul_derivativeCoefficientEnvelope (θ : ℝ) {C : (ι → ℝ) → ℝ × ℝ → ℂ}
    (hC : SymReg C) (lam : ℝ × ℝ) :
    wL θ lam * derivativeCoefficientEnvelope C lam =
      ∑' k : ℕ, ENNReal.ofReal (1/((4*k).factorial:ℝ)) * ∫⁻ α, wL θ lam * dnorm k C α lam := by
  unfold derivativeCoefficientEnvelope
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro k
  rw [lintegral_const_mul _ ((measurable_dnorm hC.smooth hC.meas k).of_uncurry_right)]
  exact mul_left_comm _ _ _

end WaveTurbulence.RegAsymp
