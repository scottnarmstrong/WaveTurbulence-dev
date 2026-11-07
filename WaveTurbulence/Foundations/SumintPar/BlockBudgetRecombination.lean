/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.ProductPowerEnvelopes
public import WaveTurbulence.Foundations.SumintPar.SourceBlockExponents

/-!
# Algebraic recombination of local block budgets and source weight decay

This is a conditional numerical helper. It does not claim the local
budgets for the actual source factors: those must be proved separately.
Once supplied, it collects their powers without changing any drafted
count or introducing a size-dependent constant.
-/

@[expose] public section
set_option autoImplicit false

open ENNReal

namespace WaveTurbulence.SumintPar

/-- Conditional numerical recombination at the exact drafted M, M₀, and M₁. -/
theorem block_budget_recombination {d : ℕ} (D : SumintDatum d)
    {A L γ η δ C β : ℝ} {N : ℕ} (hD : D.Admissible A L γ η N)
    (hd : 2 ≤ d) (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hs : Real.sqrt η ≤ gammaBase γ/8)
    (hL : 1 ≤ L) (hδ : 0 < δ) (hC : 0 ≤ C) (F : Fin D.S.I → ℝ≥0∞)
    (hF : ∀ i, F i ≤ ENNReal.ofReal (C^(D.S.n i)*δ^(-(D.S.n i:ℝ)/2)*
      L^((D.S.n i:ℝ)*((d:ℝ)-γ)+badBlockCost D γ i-(β/20)*(blockDiscrepancy D i:ℝ)))) :
    ENNReal.ofReal (L^(-(gammaWeight d γ-Real.sqrt η)*(D.M₁:ℝ)))*(∏ i, F i) ≤
      ENNReal.ofReal (C^D.S.M*δ^(-(D.S.M:ℝ)/2)*
        L^((D.S.M:ℝ)*((d:ℝ)-γ)-
          (gammaBase γ/8)*(((Finset.univ.filter (fun i => D.S.nor i = false)).card:ℝ)+(D.M₁:ℝ))-
          (β/20)*(D.M₀:ℝ))) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  let e (i : Fin D.S.I) := (D.S.n i:ℝ)*((d:ℝ)-γ)+badBlockCost D γ i-(β/20)*(blockDiscrepancy D i:ℝ)
  have hb := prod_block_power_envelopes_le D.S F e hC hδ hLp hF
  have hpow : L^(-(gammaWeight d γ-Real.sqrt η)*(D.M₁:ℝ))*(L^(∑ i, e i)) =
      L^((∑ i, e i)-(gammaWeight d γ-Real.sqrt η)*(D.M₁:ℝ)) := by
    rw [← Real.rpow_add hLp]
    congr 1
    ring
  calc
    _ ≤ ENNReal.ofReal (L^(-(gammaWeight d γ-Real.sqrt η)*(D.M₁:ℝ)))*
        ENNReal.ofReal (C^D.S.M*δ^(-(D.S.M:ℝ)/2)*L^(∑ i, e i)) := mul_le_mul' le_rfl hb
    _ = ENNReal.ofReal (C^D.S.M*δ^(-(D.S.M:ℝ)/2)*
        L^((∑ i, e i)-(gammaWeight d γ-Real.sqrt η)*(D.M₁:ℝ))) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hLp.le _)]
      congr 1
      calc
        _ = (C^D.S.M*δ^(-(D.S.M:ℝ)/2))*
          (L^(-(gammaWeight d γ-Real.sqrt η)*(D.M₁:ℝ))*L^(∑ i, e i)) := by ring
        _ = _ := by rw [hpow]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (pow_nonneg hC _) (Real.rpow_nonneg hδ.le _))
      exact Real.rpow_le_rpow_of_exponent_le hL (source_total_block_exponent_le D hD hd hγ hs β)

end WaveTurbulence.SumintPar
