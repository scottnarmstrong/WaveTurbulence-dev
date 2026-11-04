/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.RootAmplitudeLocalModels
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! # Uniform actual derivative mass of locally finite root amplitudes -/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Fixed dimensional overlap coefficient of the local root models. -/
@[expose] def rootLocalOverlapConstant (d : ℕ) : ℝ :=
  (2 * (treeRootCutoffRadius d + 1) + 1) ^ d

theorem rootLocalOverlapConstant_pos (d : ℕ) : 0 < rootLocalOverlapConstant d := by
  unfold rootLocalOverlapConstant
  have hR := treeRootCutoffRadius_nonneg d
  positivity

theorem card_rootLocalCover_le {d : ℕ} (k : Mom d) :
    ((rootLocalCover k).card : ℝ) ≤ rootLocalOverlapConstant d :=
  ApproxNT.card_intBox_le k (by have hR := treeRootCutoffRadius_nonneg d; positivity)

/-- Conditional actual derivative-mass bound from uniform single-root envelopes. The only
multiplicity is the fixed dimensional number of overlapping root cutoffs. -/
theorem lintegral_enorm_rootAmplitudeSum_derivative_le {d N j : ℕ} {U : Type*} [MeasurableSpace U]
    (μ : Measure U) (B : (Fin d → ℤ) → Mom d → U → ℂ) (v : (Fin d → ℤ) → U → ℝ)
    (hz : ∀ q k u, treeRootCutoff q k = 0 → B q k u = 0)
    (hB : ∀ q u, ContDiff ℝ N (fun k => B q k u))
    (hb : ∀ q j, j ≤ N → ∀ k u, ‖iteratedFDeriv ℝ j (fun k => B q k u) k‖ ≤ v q u)
    (hvm : ∀ q, Measurable (v q)) (hvn : ∀ q u, 0 ≤ v q u)
    {V : ℝ≥0∞} (hv : ∀ q, (∫⁻ u, ENNReal.ofReal (v q u) ∂μ) ≤ V)
    (hj : j ≤ N) (k : Mom d) :
    (∫⁻ u, ‖iteratedFDeriv ℝ j (fun k => rootAmplitudeSum B k u) k‖ₑ ∂μ) ≤
      ENNReal.ofReal (rootLocalOverlapConstant d) * V := by
  have hpoint (u : U) : ‖iteratedFDeriv ℝ j (fun k => rootAmplitudeSum B k u) k‖ ≤
      rootAmplitudeModelEnvelope v k j u := by
    rw [iteratedFDeriv_rootAmplitudeSum_eq_model B hz]
    exact norm_iteratedFDeriv_rootAmplitudeModel_le B v hB hb hj k k u
  calc
    _ ≤ ∫⁻ u, ENNReal.ofReal (rootAmplitudeModelEnvelope v k j u) ∂μ := by
      apply lintegral_mono
      intro u
      simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (hpoint u)
    _ = ∫⁻ u, ∑ q ∈ rootLocalCover k, ENNReal.ofReal (v q u) ∂μ := by
      apply lintegral_congr
      intro u
      exact ENNReal.ofReal_sum_of_nonneg (fun q _ => hvn q u)
    _ = ∑ q ∈ rootLocalCover k, ∫⁻ u, ENNReal.ofReal (v q u) ∂μ :=
      lintegral_finsetSum _ (fun q _ => ENNReal.measurable_ofReal.comp (hvm q))
    _ ≤ ∑ _q ∈ rootLocalCover k, V := Finset.sum_le_sum (fun q _ => hv q)
    _ = ((rootLocalCover k).card : ℝ≥0∞) * V := by simp
    _ ≤ _ := by
      apply mul_le_mul' _ le_rfl
      simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (card_rootLocalCover_le k)

end WaveTurbulence.Incoh
