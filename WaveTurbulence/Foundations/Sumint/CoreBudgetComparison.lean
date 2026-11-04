/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.CorePowerBudget

/-!
# Numerical comparison with the common source core budget

These scalar lemmas only collect the explicit powers already supplied
by source mass estimates. They introduce no hypothesis on a source norm.
-/

public section
namespace WaveTurbulence.Sumint

/-- A coefficient and power estimate fits the common core budget at its exact input arity. -/
theorem coefficient_power_le_sourceCorePowerBudget {d : ℕ} (D : SumintDatum d)
    {G L γ δ C E : ℝ} (hL : 1 ≤ L) (hδ : 0 < δ) (hC0 : 0 ≤ C)
    (b : FactorIdx D.S) (n : ℕ) (hn : sourceCoreArity D b = n)
    (hC : C ≤ G^n) (hE : E ≤ (n:ℝ)*((d:ℝ)-γ)+sourceCoreBadCost D γ b) :
    C*δ^(-(n:ℝ)/2)*L^E ≤ sourceCorePowerBudget D G L γ δ b := by
  unfold sourceCorePowerBudget
  rw [hn]
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hδ.le _)
  · exact Real.rpow_le_rpow_of_exponent_le hL hE
  · exact Real.rpow_nonneg (zero_le_one.trans hL) _
  · exact mul_nonneg (hC0.trans hC) (Real.rpow_nonneg hδ.le _)

/-- A unit-coefficient power estimate fits the core budget after inserting its permitted delta cost. -/
theorem power_le_sourceCorePowerBudget {d : ℕ} (D : SumintDatum d)
    {G L γ δ E : ℝ} (hG : 1 ≤ G) (hL : 1 ≤ L) (hδ : δ ∈ Set.Ioc (0:ℝ) 1)
    (b : FactorIdx D.S) (hE : E ≤ (sourceCoreArity D b:ℝ)*((d:ℝ)-γ)+sourceCoreBadCost D γ b) :
    L^E ≤ sourceCorePowerBudget D G L γ δ b := by
  have hdel : 1 ≤ δ^(-(sourceCoreArity D b:ℝ)/2) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ.1 hδ.2
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (by norm_num))
  calc
    _ ≤ 1*δ^(-(sourceCoreArity D b:ℝ)/2)*L^E := by
      rw [one_mul]
      exact le_mul_of_one_le_left (Real.rpow_nonneg (zero_le_one.trans hL) _) hdel
    _ ≤ _ := coefficient_power_le_sourceCorePowerBudget D hL hδ.1 zero_le_one b _ rfl
      (one_le_pow₀ hG) hE

end WaveTurbulence.Sumint
