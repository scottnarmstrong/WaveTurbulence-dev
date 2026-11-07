/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.PowerComparison
public import WaveTurbulence.Foundations.SumintPar.ExponentMargins

/-!
# Minimum first-pair envelopes keep both source gains

This conditional numerical helper is used after the actual source
first-pair envelope and linear estimates have been proved. Taking the
minimum with the pair-incoherence envelope gives a quarter-gammaBase
bad gain and beta/20, retaining an additional positive reserve.
-/

@[expose] public section
set_option autoImplicit false

open ENNReal

namespace WaveTurbulence.SumintPar

/-- Numerical bad/incoherent comparison for the uniform first-pair minimum envelope. -/
theorem first_pair_minimum_bound {F E : ℝ≥0∞} {L γ β : ℝ} (d : ℕ) (hL : 1 ≤ L)
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1)
    (hbad : F*E ≤ ENNReal.ofReal (L^(3*((d:ℝ)-γ)-gammaBase γ/2)))
    (hlinear : F ≤ ENNReal.ofReal (L^((d:ℝ)-γ+3*gammaBase γ/2))) :
    F*min E (ENNReal.ofReal (L^(2*((d:ℝ)-γ)-β/2))) ≤
      ENNReal.ofReal (L^(3*((d:ℝ)-γ)-gammaBase γ/4-β/20)) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hb := gammaBase_pos hγ
  have hcomp := mul_min_le_interpolated_power hLp (by norm_num : (1/10:ℝ) ∈ Set.Icc (0:ℝ) 1)
    hbad hlinear (c := 2*((d:ℝ)-γ)-β/2)
  apply hcomp.trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow_of_exponent_le hL
  linarith only [hb]

end WaveTurbulence.SumintPar
