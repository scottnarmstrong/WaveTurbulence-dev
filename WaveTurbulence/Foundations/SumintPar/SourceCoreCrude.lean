/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceLocalTrivial
public import WaveTurbulence.Foundations.SumintPar.SourceCoreLocalBox
public import WaveTurbulence.Foundations.SumintPar.CoreArityProducts

/-!
# Counting bounds for concrete source cores touched by fixed times

Only affected cores use these bounds. Their old-factor count is at most
their input arity, so every gap constant has a bounded total exponent.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set ENNReal
open scoped Classical
namespace WaveTurbulence.SumintPar

/-- Every old factor has at least one native coordinate. -/
theorem one_le_factorArity (S : SumintShape) (a : FactorIdx S) : 1 ≤ factorArity S a := by
  rcases a with i | (a | i) <;> simp [factorArity]

/-- The number of old factors in a coarse core is at most its coordinate arity. -/
theorem card_sourceCore_factors_le {d : ℕ} (D : SumintDatum d) (b : FactorIdx D.S) :
    Fintype.card {a : FactorIdx D.S // sourceCoreGroup D a = b} ≤ sourceCoreArity D b := by
  rw [← sum_factorArity_sourceCore]
  calc
    _ = ∑ _a : {a : FactorIdx D.S // sourceCoreGroup D a = b}, 1 := by simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one]
    _ ≤ _ := Finset.sum_le_sum (fun a _ => one_le_factorArity D.S a.1)

/-- The actual raw core is bounded by its literal input-count power on the native source box. -/
theorem sourceCoreRawNorm_le_count {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {N : ℕ} (hD : D.Admissible A L γ η N) (hL : 0 < L) (hη : 0 ≤ 1-3*η)
    (δ : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c : ℝ)
    {h : ℝ} (hh : h ≤ 1) (b : FactorIdx D.S) (z : SourceCoreCoordinate D b → ℝ)
    (hz : z ∈ sourceCoreTimeBox D c h b) :
    sourceCoreRawNorm D L γ δ η p ν r t b z ≤
      ENNReal.ofReal ((max 1 (((N:ℝ)+2)^(1-3*η)))^(sourceCoreArity D b)*
        (8*L+1)^(d*sourceCoreArity D b)) := by
  let K := max 1 (((N:ℝ)+2)^(1-3*η))
  have hK : 1 ≤ K := le_max_left _ _
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  calc
    _ ≤ ∏ a : {a : FactorIdx D.S // sourceCoreGroup D a = b},
        ENNReal.ofReal (K*(8*L+1)^(d*factorArity D.S a.1)) := by
      apply Finset.prod_le_prod
      intro a _
      exact ENNReal.ofReal_le_ofReal (sourceTimeNormFactor_le_window_count D hD hL hη δ p ν r t c hh a.1 _
        (sourceCoreOldTimes_mem_intervals D c h b z hz a))
    _ = ENNReal.ofReal (K^(Fintype.card {a : FactorIdx D.S // sourceCoreGroup D a = b})*
        (8*L+1)^(d*sourceCoreArity D b)) := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => mul_nonneg hK0 (by positivity)),Finset.prod_mul_distrib,
        Finset.prod_const,Finset.card_univ,prod_counting_sourceCore]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hK (card_sourceCore_factors_le D b)) (by positivity))

/-- The external coarse multiplier never increases norms when the output difference is at most one. -/
theorem sourceCoreMultiplier_le_one {d : ℕ} (D : SumintDatum d) (r : Mom d)
    (hr : ‖r‖ ≤ 1) (b : FactorIdx D.S) : sourceCoreMultiplier D r b ≤ 1 := by
  rcases b with i | b
  · change caseBMultiplier D r i ≤ 1
    unfold caseBMultiplier
    split_ifs
    · exact (ENNReal.ofReal_le_ofReal hr).trans_eq ENNReal.ofReal_one
    · exact le_rfl
  · exact le_rfl

/-- The concrete masked core has its actual bounded-arity counting estimate. -/
theorem sourceCoreNormFactor_le_count {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {N : ℕ} (hD : D.Admissible A L γ η N) (hL : 0 < L) (hη : 0 ≤ 1-3*η)
    (δ : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (hr : ‖r‖ ≤ 1)
    (t c : ℝ) {h : ℝ} (hh : h ≤ 1) (b : FactorIdx D.S) (z : SourceCoreCoordinate D b → ℝ) :
    sourceCoreNormFactor D L γ δ η p ν r t c h b z ≤
      ENNReal.ofReal ((max 1 (((N:ℝ)+2)^(1-3*η)))^(sourceCoreArity D b)*
        (8*L+1)^(d*sourceCoreArity D b)) := by
  by_cases hz : z ∈ sourceCoreTimeBox D c h b ∩ {z | sourceCoreOrdering D b z}
  · rw [sourceCoreNormFactor,Set.indicator_of_mem hz]
    exact (mul_le_mul' (sourceCoreMultiplier_le_one D r hr b) le_rfl).trans
      ((one_mul _).le.trans (sourceCoreRawNorm_le_count D hD hL hη δ p ν r t c hh b z hz.1))
  · rw [sourceCoreNormFactor,Set.indicator_of_notMem hz]
    exact bot_le

/-- Every touched core has an unconditional explicit mixed-measure mass estimate. -/
theorem lintegral_sourceCore_fixed_count_le {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {N : ℕ} (hD : D.Admissible A L γ η N) (hL : 0 < L) (hη : 0 ≤ 1-3*η)
    (δ : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (hr : ‖r‖ ≤ 1)
    (t c : ℝ) {h : ℝ} (hh : h ≤ 1) (b : FactorIdx D.S) (s : Set D.S.TVar) (x : D.S.TVar → ℝ) :
    (∫⁻ z, sourceCoreNormFactor D L γ δ η p ν r t c h b z
      ∂Measure.pi (fun j => fixedCoordinateMeasure s x (sourceCoreCoordinateTimeEquiv D ⟨b,j⟩))) ≤
      ENNReal.ofReal ((max 1 (((N:ℝ)+2)^(1-3*η)))^(sourceCoreArity D b)*
        (8*L+1)^(d*sourceCoreArity D b))*ENNReal.ofReal (3^(sourceCoreArity D b):ℝ) :=
  lintegral_sourceCore_fixed_le D L γ δ η p ν r t c hh b s x _
    (fun z _ => sourceCoreNormFactor_le_count D hD hL hη δ p ν r hr t c hh b z)

end WaveTurbulence.SumintPar
