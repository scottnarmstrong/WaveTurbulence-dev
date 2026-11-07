/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceCoreDomain
public import WaveTurbulence.Foundations.SumintPar.FiberBigOperators
public import WaveTurbulence.Foundations.SumintPar.WeightedCutoffInput

/-!
# Exact coarse-core product for the actual source input

On the actual local static domain every interval and ordering mask is
satisfied. Regrouping the original norm factors and distributing the
literal external momentum multiplier gives the actual weighted input
norm. Outside that domain the zero extension is bounded by the same
nonnegative independent core product.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set ENNReal
open scoped Classical

namespace WaveTurbulence.SumintPar

/-- Regrouping raw core norms preserves exactly the actual cutoff-sum norm. -/
theorem prod_sourceCoreRawNorm_eq {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (u : D.S.TVar → ℝ) :
    (∏ b : FactorIdx D.S, sourceCoreRawNorm D L γ δ η p ν r t b (sourceCoreTimeGrouping D u b)) =
      ‖cutoffPhaseSum D L γ δ η p ν r t u‖ₑ := by
  have ht (b : FactorIdx D.S) (a : {a : FactorIdx D.S // sourceCoreGroup D a = b}) :
      sourceCoreOldTimes D b (sourceCoreTimeGrouping D u b) a = timeCoordinateGrouping D.S u a.1 := by
    funext j
    exact (sourceCoreTimeGrouping_apply D u b a.1 a.2 j).trans (timeCoordinateGrouping_apply D.S u a.1 j).symm
  unfold sourceCoreRawNorm
  simp_rw [ht]
  trans ∏ a : FactorIdx D.S, ENNReal.ofReal (sourceTimeNormFactor D L γ δ η p ν r t a (timeCoordinateGrouping D.S u a))
  · exact prod_fiber_subtype (sourceCoreGroup D) (fun a => ENNReal.ofReal
      (sourceTimeNormFactor D L γ δ η p ν r t a (timeCoordinateGrouping D.S u a)))
  rw [← ofReal_norm,norm_cutoffPhaseSum_eq_time_factor_product D hL γ δ η p ν r t u,
    ENNReal.ofReal_prod_of_nonneg (fun a _ => sourceTimeNormFactor_nonneg D L γ δ η p ν r t a _)]

/-- The coarse external multipliers are exactly the literal source case-(b) norm power. -/
theorem prod_sourceCoreMultiplier {d : ℕ} (D : SumintDatum d) (r : Mom d) :
    (∏ b : FactorIdx D.S, sourceCoreMultiplier D r b) =
      ENNReal.ofReal (‖r‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card) := by
  rw [Fintype.prod_sum_type]
  simp only [sourceCoreMultiplier,Finset.prod_const_one,mul_one]
  exact prod_caseBMultiplier D r

/-- On the actual local source domain the concrete core product is exactly its original input norm. -/
theorem prod_sourceCoreNormFactor_eq_on_local {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {N : ℕ} (hD : D.Admissible A L γ η N) (hL : 0 < L)
    (δ : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
    (u : D.S.TVar → ℝ) (hu : u ∈ localInputTimeDomain D c h) :
    (∏ b : FactorIdx D.S, sourceCoreNormFactor D L γ δ η p ν r t c h b (sourceCoreTimeGrouping D u b)) =
      ENNReal.ofReal (‖r‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card)*
        ‖cutoffPhaseSum D L γ δ η p ν r t u‖ₑ := by
  simp_rw [sourceCoreNormFactor_eq_on_local D hD δ p ν r t c h u hu]
  rw [Finset.prod_mul_distrib,prod_sourceCoreMultiplier,prod_sourceCoreRawNorm_eq D hL]

/-- The actual weighted source input's zero extension is dominated by the independent concrete core product. -/
theorem weightedCutoffInput_indicator_le_core_product {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {N : ℕ} (hD : D.Admissible A L γ η N) (hL : 0 < L)
    (δ : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (c h : ℝ)
    (u : D.S.TVar → ℝ) :
    (localInputTimeDomain D c h).indicator (fun u => ‖weightedCutoffInput D L γ δ η p ν r u‖ₑ) u ≤
      ENNReal.ofReal (sourceWeightDecay D L γ η)*
        ∏ b : FactorIdx D.S, sourceCoreNormFactor D L γ δ η p ν r 0 c h b (sourceCoreTimeGrouping D u b) := by
  by_cases hu : u ∈ localInputTimeDomain D c h
  · rw [Set.indicator_of_mem hu,prod_sourceCoreNormFactor_eq_on_local D hD hL δ p ν r 0 c h u hu,
      enorm_weightedCutoffInput D hL]
  · rw [Set.indicator_of_notMem hu]
    exact bot_le

end WaveTurbulence.SumintPar
