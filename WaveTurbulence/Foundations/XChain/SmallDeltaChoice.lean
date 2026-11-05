/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SmallDeltaConsequences
/-! The small-delta restriction is chosen after nu and before D, exactly as required by the source prefix. -/
public section
namespace WaveTurbulence.Induct

theorem delta_half_power_le_of_threshold {δ ν : ℝ} (hδ : 0 < δ) (hν : 0 < ν)
    (hsize : δ ≤ Real.exp (-8000000 / ν)) : δ ^ (ν / 2) ≤ Real.exp (-4000000) := by
  have hlog : Real.log δ ≤ -8000000 / ν := (Real.log_le_iff_le_exp hδ).mpr hsize
  have hm := mul_le_mul_of_nonneg_right hlog (div_nonneg hν.le (by norm_num : (0 : ℝ) ≤ 2))
  have he : (-8000000 / ν) * (ν / 2) = (-4000000 : ℝ) := by
    field_simp
    ring
  rw [Real.rpow_def_of_pos hδ]
  exact Real.exp_le_exp.mpr (hm.trans_eq he)

end WaveTurbulence.Induct
