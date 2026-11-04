/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceCoreExactArities
public import WaveTurbulence.Foundations.Sumint.SourceBlockExponents

/-!
# Uniform numerical budgets for actual source cores

Only distinguished linear labels carry a bad-block cost. Every budget
is at least one: this allows unused touched-core budgets to be inserted
when estimating the product of untouched cores, without division by a
possibly vanishing oscillatory mass.
-/

public section
open scoped Classical
namespace WaveTurbulence.Sumint

/-- The source bad-block exponent belongs to its distinguished coarse core. -/
@[expose] noncomputable def sourceCoreBadCost {d : ℕ} (D : SumintDatum d) (γ : ℝ) : FactorIdx D.S → ℝ
  | .inl i => badBlockCost D γ i
  | .inr _ => 0

/-- The numerical scale budget of a concrete source core. -/
@[expose] noncomputable def sourceCorePowerBudget {d : ℕ} (D : SumintDatum d) (G L γ δ : ℝ)
    (b : FactorIdx D.S) : ℝ :=
  G^(sourceCoreArity D b)*δ^(-(sourceCoreArity D b:ℝ)/2)*
    L^((sourceCoreArity D b:ℝ)*((d:ℝ)-γ)+sourceCoreBadCost D γ b)

/-- Coarse bad costs sum to exactly the original block bad costs. -/
theorem sum_sourceCoreBadCost {d : ℕ} (D : SumintDatum d) (γ : ℝ) :
    (∑ b : FactorIdx D.S, sourceCoreBadCost D γ b) = ∑ i : Fin D.S.I, badBlockCost D γ i := by
  rw [Fintype.sum_sum_type]
  simp only [sourceCoreBadCost,Finset.sum_const_zero,add_zero]

/-- Each source bad-block cost is bounded below by the fixed quarter-base loss. -/
theorem badBlockCost_lower {d : ℕ} (D : SumintDatum d) {γ : ℝ} (hγ : γ ∈ Set.Ioo (0:ℝ) 1)
    (i : Fin D.S.I) : -gammaBase γ/4 ≤ badBlockCost D γ i := by
  have hg := gammaBase_pos hγ
  unfold badBlockCost
  split_ifs <;> linarith only [hg]

/-- Every distinguished linear core contains its original scalar input. -/
theorem one_le_sourceCoreArity_linear {d : ℕ} (D : SumintDatum d) (i : Fin D.S.I) :
    1 ≤ sourceCoreArity D (.inl i) := by
  have hn : Nonempty (SourceCoreCoordinate D (.inl i)) := ⟨⟨⟨.inl i,rfl⟩,0⟩⟩
  exact Fintype.card_pos_iff.mpr hn

/-- The exponent in every coarse budget is nonnegative in the source dimension range. -/
theorem sourceCoreBudget_exponent_nonneg {d : ℕ} (D : SumintDatum d) (hd : 2 ≤ d)
    {γ : ℝ} (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (b : FactorIdx D.S) :
    0 ≤ (sourceCoreArity D b:ℝ)*((d:ℝ)-γ)+sourceCoreBadCost D γ b := by
  have hdim : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hbase : 0 ≤ (d:ℝ)-γ := by linarith only [hdim,hγ.2]
  have hg : gammaBase γ ≤ γ := min_le_left _ _
  rcases b with i | b
  · have ha : (1:ℝ) ≤ sourceCoreArity D (.inl i) := by exact_mod_cast one_le_sourceCoreArity_linear D i
    have hm := mul_le_mul_of_nonneg_right ha hbase
    have hc := badBlockCost_lower D hγ i
    change 0 ≤ (sourceCoreArity D (.inl i):ℝ)*((d:ℝ)-γ)+badBlockCost D γ i
    linarith only [hm,hc,hg,hdim,hγ.2]
  · exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) hbase) le_rfl

/-- Every numerical source-core budget is at least one. -/
theorem one_le_sourceCorePowerBudget {d : ℕ} (D : SumintDatum d) (hd : 2 ≤ d)
    {G L γ δ : ℝ} (hG : 1 ≤ G) (hL : 1 ≤ L) (hγ : γ ∈ Set.Ioo (0:ℝ) 1)
    (hδ : δ ∈ Set.Ioc (0:ℝ) 1) (b : FactorIdx D.S) : 1 ≤ sourceCorePowerBudget D G L γ δ b := by
  have hpow : 1 ≤ G^(sourceCoreArity D b) := one_le_pow₀ hG
  have hdel : 1 ≤ δ^(-(sourceCoreArity D b:ℝ)/2) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ.1 hδ.2 (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (by norm_num))
  have hscale : 1 ≤ L^((sourceCoreArity D b:ℝ)*((d:ℝ)-γ)+sourceCoreBadCost D γ b) :=
    Real.one_le_rpow hL (sourceCoreBudget_exponent_nonneg D hd hγ b)
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hpow hdel) hscale

end WaveTurbulence.Sumint
