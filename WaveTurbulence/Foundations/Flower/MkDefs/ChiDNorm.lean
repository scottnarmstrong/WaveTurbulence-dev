/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkDefs.Bounds

/-! # The normalized selected filter (ruling R179, F-B3s-1)

`chiD u = -u χ₀'(u)` has supremum `> 1` (`χ₀` drops from `1` to `0` on `[1/2, 1]`). The filters of a sound marked
piece must have supremum at most `1` (`SoundMKFull.filt_ok`), so the filter of a residual selected vertex is the
normalized `chiD / chiDNorm`, with `chiDNorm := max 1 chiDConst`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace WaveTurbulence.Flower.MkDefs

/-- The normalization constant of the selected filter (an absolute constant, at least `1`). -/
def chiDNorm : ℝ := max 1 chiDConst

theorem one_le_chiDNorm : 1 ≤ chiDNorm := le_max_left _ _

theorem chiDNorm_pos : 0 < chiDNorm := lt_of_lt_of_le one_pos one_le_chiDNorm

theorem abs_chiD_le_chiDNorm (u : ℝ) : |chiD u| ≤ chiDNorm := (abs_chiD_le u).trans (le_max_right _ _)

/-- The normalized selected filter `chiD / chiDNorm` (real-valued). -/
def chiDN (u : ℝ) : ℝ := chiD u / chiDNorm

theorem abs_chiDN_le_one (u : ℝ) : |chiDN u| ≤ 1 := by
  unfold chiDN
  rw [abs_div, abs_of_pos chiDNorm_pos, div_le_one chiDNorm_pos]
  exact abs_chiD_le_chiDNorm u

theorem norm_chiDN_le_one (u : ℝ) : ‖((chiDN u : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_chiDN_le_one u

end WaveTurbulence.Flower.MkDefs
