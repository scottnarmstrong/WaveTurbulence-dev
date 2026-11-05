/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.RemainderScaleAbsorption
/-! One small-delta choice supplies all geometric inequalities used by the error bounds. -/
public section
namespace WaveTurbulence.Induct

theorem small_delta_consequences {δ ν : ℝ} (hδ : 0 < δ)
    (hq : δ ^ (ν / 2) ≤ Real.exp (-4000000)) :
    δ ^ (ν / 2) ≤ 1 / 2 ∧ δ ^ ν ≤ 1 / 2 ∧ δ ^ (2 * ν) ≤ 1 / 2 ∧
      δ ^ ν ≤ Real.exp (-21) := by
  let q := δ ^ (ν / 2)
  have hq0 : 0 ≤ q := Real.rpow_nonneg hδ.le _
  have hqhalf : q ≤ 1 / 2 := hq.trans ((Real.exp_le_exp.mpr (by norm_num : (-4000000 : ℝ) ≤ -1)).trans exp_neg_one_le_half)
  have hq1 : q ≤ 1 := by linarith
  have he2 : q ^ 2 = δ ^ ν := by
    dsimp [q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    congr 1
    norm_num
  have he4 : q ^ 4 = δ ^ (2 * ν) := by
    dsimp [q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    congr 1
    norm_num
    ring
  have hq2 : q ^ 2 ≤ q := by nlinarith
  have hq4 : q ^ 4 ≤ q := by
    exact (pow_le_pow_of_le_one hq0 hq1 (by omega : 1 ≤ 4)).trans_eq (pow_one q)
  exact ⟨hqhalf, he2 ▸ hq2.trans hqhalf, he4 ▸ hq4.trans hqhalf,
    he2 ▸ hq2.trans (hq.trans (Real.exp_le_exp.mpr (by norm_num)))⟩

end WaveTurbulence.Induct
