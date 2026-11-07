/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.CorePowerBudget
public import WaveTurbulence.Foundations.SumintPar.ProductPowerEnvelopes
public import WaveTurbulence.Foundations.SumintPar.WeightedCutoffInput

/-!
# Numerical recombination of all coarse source budgets

The arities sum to the literal M and the bad costs sum to the original
block costs. Weight decay therefore retains the established bad and M1
gains, with no discrepancy gain required at the positive endpoint.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ENNReal
namespace WaveTurbulence.SumintPar

/-- The total coarse exponent is exactly the original block exponent with zero discrepancy cost. -/
theorem sum_sourceCoreBudget_exponent {d : ℕ} (D : SumintDatum d) (γ : ℝ) :
    (∑ b : FactorIdx D.S, ((sourceCoreArity D b:ℝ)*((d:ℝ)-γ)+sourceCoreBadCost D γ b)) =
      ∑ i : Fin D.S.I, ((D.S.n i:ℝ)*((d:ℝ)-γ)+badBlockCost D γ i) := by
  rw [Finset.sum_add_distrib,← Finset.sum_mul,sum_sourceCoreBadCost,
    Finset.sum_add_distrib,← Finset.sum_mul]
  congr 2
  exact_mod_cast sum_sourceCoreArity D

/-- The literal finite product of all numerical source-core budgets retains the source weight gain. -/
theorem weighted_prod_sourceCorePowerBudget_le {d : ℕ} (D : SumintDatum d)
    {A G L γ η δ : ℝ} {N : ℕ} (hD : D.Admissible A L γ η N)
    (hd : 2 ≤ d) (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hs : Real.sqrt η ≤ gammaBase γ/8)
    (hG : 0 ≤ G) (hL : 1 ≤ L) (hδ : 0 < δ) :
    ENNReal.ofReal (sourceWeightDecay D L γ η) *
      (∏ b : FactorIdx D.S, ENNReal.ofReal (sourceCorePowerBudget D G L γ δ b)) ≤
      ENNReal.ofReal (G^D.S.M*δ^(-(D.S.M:ℝ)/2)*
        L^((D.S.M:ℝ)*((d:ℝ)-γ)-
          (gammaBase γ/8)*(((Finset.univ.filter (fun i => D.S.nor i = false)).card:ℝ)+(D.M₁:ℝ)))) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  let e (b : FactorIdx D.S) := (sourceCoreArity D b:ℝ)*((d:ℝ)-γ)+sourceCoreBadCost D γ b
  have hb := prod_local_power_envelopes_le
    (fun b => ENNReal.ofReal (sourceCorePowerBudget D G L γ δ b))
    (fun b => G^(sourceCoreArity D b)) (fun b => (sourceCoreArity D b:ℝ)/2) e hδ hLp
    (fun b => pow_nonneg hG _) (by intro b; simp only [sourceCorePowerBudget,neg_div,e]; exact le_rfl)
  have hsum : (∑ b : FactorIdx D.S, (sourceCoreArity D b:ℝ)/2) = (D.S.M:ℝ)/2 := by
    rw [← Finset.sum_div]
    congr 1
    exact_mod_cast sum_sourceCoreArity D
  rw [Finset.prod_pow_eq_pow_sum,sum_sourceCoreArity,hsum] at hb
  simp only [← neg_div] at hb
  have hexp := source_total_block_exponent_le D hD hd hγ hs 0
  simp only [zero_div,zero_mul,sub_zero] at hexp
  have he : (∑ b, e b)-(gammaWeight d γ-Real.sqrt η)*(D.M₁:ℝ) ≤
      (D.S.M:ℝ)*((d:ℝ)-γ)-
        (gammaBase γ/8)*(((Finset.univ.filter (fun i => D.S.nor i = false)).card:ℝ)+(D.M₁:ℝ)) := by
    rw [show (∑ b, e b) = ∑ i : Fin D.S.I, ((D.S.n i:ℝ)*((d:ℝ)-γ)+badBlockCost D γ i) from
      sum_sourceCoreBudget_exponent D γ]
    exact hexp
  apply (mul_le_mul' le_rfl hb).trans
  have hw : 0 ≤ sourceWeightDecay D L γ η := Real.rpow_nonneg hLp.le _
  rw [← ENNReal.ofReal_mul hw]
  apply ENNReal.ofReal_le_ofReal
  have hp : sourceWeightDecay D L γ η*(G^D.S.M*δ^(-(D.S.M:ℝ)/2)*L^(∑ b, e b)) =
      G^D.S.M*δ^(-(D.S.M:ℝ)/2)*L^((∑ b, e b)-(gammaWeight d γ-Real.sqrt η)*(D.M₁:ℝ)) := by
    unfold sourceWeightDecay
    rw [← mul_assoc, mul_comm (L^(-(gammaWeight d γ-Real.sqrt η)*(D.M₁:ℝ))) _,mul_assoc,
      ← Real.rpow_add hLp]
    congr 2
    ring
  rw [hp]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL he)
    (mul_nonneg (pow_nonneg hG _) (Real.rpow_nonneg hδ.le _))

end WaveTurbulence.SumintPar
