/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.CutoffPhaseSumRegularity
public import WaveTurbulence.Foundations.Sumint.ExponentMargins

/-!
# The weighted actual input to the explicit rectangular kernel

The source weight-decay factor and the literal external case-(b) norm
power are included in the input coefficient. This is a scalar multiple
of the actual cutoff lattice sum; its native time integrability and its
exact nonnegative input mass are proved, not assumed.
-/

public section

open MeasureTheory Set ENNReal

namespace WaveTurbulence.Sumint

/-- The literal scalar source weight decay for the full multiplicity M₁. -/
@[expose] noncomputable def sourceWeightDecay {d : ℕ} (D : SumintDatum d) (L γ η : ℝ) : ℝ :=
  L^(-(gammaWeight d γ-Real.sqrt η)*(D.M₁:ℝ))

/-- The actual cutoff input with source weight and external case-(b) scalars included. -/
@[expose] noncomputable def weightedCutoffInput {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (u : D.S.TVar → ℝ) : ℂ :=
  ((sourceWeightDecay D L γ η*
    ‖r‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card : ℝ):ℂ)*
      cutoffPhaseSum D L γ δ η p ν r 0 u

/-- The weighted actual input is measurable in the input-time vector. -/
theorem measurable_weightedCutoffInput {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) :
    Measurable (weightedCutoffInput D L γ δ η p ν r) :=
  measurable_const.mul (measurable_cutoffPhaseSum D hL γ δ η p ν r 0)

/-- The weighted actual input is genuinely integrable on the local source domain. -/
theorem integrableOn_weightedCutoffInput {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (γ δ η : ℝ) (hη : η ≤ 1/3) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d)
    (r : Mom d) (c h : ℝ) :
    IntegrableOn (weightedCutoffInput D L γ δ η p ν r) (localInputTimeDomain D c h) :=
  (integrableOn_cutoffPhaseSum_localDomain D hL γ δ η hη p ν r 0 c h).const_mul _

/-- Exact norm of the actual weighted input coefficient. -/
theorem enorm_weightedCutoffInput {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d)
    (r : Mom d) (u : D.S.TVar → ℝ) :
    ‖weightedCutoffInput D L γ δ η p ν r u‖ₑ =
      ENNReal.ofReal (sourceWeightDecay D L γ η)*
        (ENNReal.ofReal (‖r‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card)*
          ‖cutoffPhaseSum D L γ δ η p ν r 0 u‖ₑ) := by
  have hw : 0 ≤ sourceWeightDecay D L γ η := Real.rpow_nonneg hL.le _
  have hr : 0 ≤ ‖r‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card := by positivity
  unfold weightedCutoffInput
  rw [enorm_mul,← ofReal_norm,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hw hr),
    ENNReal.ofReal_mul hw]
  ac_rfl

/-- Exact weighted input mass for the actual local source domain. -/
theorem lintegral_enorm_weightedCutoffInput {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d)
    (r : Mom d) (c h : ℝ) :
    (∫⁻ u in localInputTimeDomain D c h, ‖weightedCutoffInput D L γ δ η p ν r u‖ₑ) =
      ENNReal.ofReal (sourceWeightDecay D L γ η)*
        (ENNReal.ofReal (‖r‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card)*
          (∫⁻ u in localInputTimeDomain D c h, ‖cutoffPhaseSum D L γ δ η p ν r 0 u‖ₑ)) := by
  simp_rw [enorm_weightedCutoffInput D hL]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end WaveTurbulence.Sumint
