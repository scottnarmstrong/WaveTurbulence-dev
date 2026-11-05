/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ForestBracketWeightSum
/-! The explicit finite tree/partition/lattice factor in the proved E1 and E2 estimates. -/
@[expose] public section
namespace WaveTurbulence.Induct

noncomputable def graftEnvelope (d w N : ℕ) (L b C : ℝ) : ℝ :=
  let H := w * (2 * N + 1)
  ((3 ^ (3 * N + 1) : ℝ) ^ w * ((2 ^ H : ℝ) ^ H)) *
    ((2 * C) ^ H * (2 ^ H : ℝ) ^ b *
      (max 1 (∑' m : Fin d → ℤ, jbr (latticePoint L m) ^ (-b))) ^ H)

theorem graftEnvelope_nonneg (d w N : ℕ) (L b C : ℝ) (hC : 0 ≤ C) :
    0 ≤ graftEnvelope d w N L b C := by
  unfold graftEnvelope
  apply mul_nonneg
  · positivity
  · exact mul_nonneg (mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) hC) _)
      (Real.rpow_nonneg (by positivity) _)) (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)

end WaveTurbulence.Induct
