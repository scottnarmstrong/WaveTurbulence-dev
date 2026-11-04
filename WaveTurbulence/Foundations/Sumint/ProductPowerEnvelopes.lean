/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.BlockMassProducts
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Multiplying finite local power envelopes

This algebraic helper keeps all local constants, delta powers, and
lattice exponents explicit. It is independent of the source estimates;
those supply the bounds before the product is collected.
-/

public section

open ENNReal

namespace WaveTurbulence.Sumint

/-- Finite local power envelopes multiply with exactly summed exponents. -/
theorem prod_local_power_envelopes_le {ι : Type*} [Fintype ι]
    (F : ι → ℝ≥0∞) (C q e : ι → ℝ) {δ L : ℝ} (hδ : 0 < δ) (hL : 0 < L)
    (hC : ∀ i, 0 ≤ C i)
    (hF : ∀ i, F i ≤ ENNReal.ofReal (C i*δ^(-q i)*L^(e i))) :
    (∏ i, F i) ≤ ENNReal.ofReal ((∏ i, C i)*δ^(-(∑ i, q i))*L^(∑ i, e i)) := by
  calc
    _ ≤ ∏ i, ENNReal.ofReal (C i*δ^(-q i)*L^(e i)) :=
      Finset.prod_le_prod (fun i _ => hF i)
    _ = ENNReal.ofReal (∏ i, C i*δ^(-q i)*L^(e i)) :=
      (ENNReal.ofReal_prod_of_nonneg (fun i _ =>
        mul_nonneg (mul_nonneg (hC i) (Real.rpow_nonneg hδ.le _)) (Real.rpow_nonneg hL.le _))).symm
    _ = _ := by
      congr 1
      rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,
        ← Real.rpow_sum_of_pos hδ,← Real.rpow_sum_of_pos hL,Finset.sum_neg_distrib]

/-- The per-block constant and delta cost collect at the literal total input arity. -/
theorem prod_block_power_envelopes_le (S : SumintShape) (F : Fin S.I → ℝ≥0∞)
    (e : Fin S.I → ℝ) {C δ L : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) (hL : 0 < L)
    (hF : ∀ i, F i ≤ ENNReal.ofReal (C^(S.n i)*δ^(-(S.n i:ℝ)/2)*L^(e i))) :
    (∏ i, F i) ≤ ENNReal.ofReal (C^S.M*δ^(-(S.M:ℝ)/2)*L^(∑ i, e i)) := by
  have hb := prod_local_power_envelopes_le F (fun i => C^(S.n i))
    (fun i => (S.n i:ℝ)/2) e hδ hL (fun i => pow_nonneg hC _) (by intro i; simpa only [neg_div] using hF i)
  apply hb.trans_eq
  congr 1
  rw [Finset.prod_pow_eq_pow_sum]
  have hsum : (∑ i : Fin S.I, (S.n i:ℝ)/2) = (S.M:ℝ)/2 := by
    rw [← Finset.sum_div]
    congr 1
    norm_cast
  rw [hsum]
  simp only [neg_div]
  rfl

end WaveTurbulence.Sumint
