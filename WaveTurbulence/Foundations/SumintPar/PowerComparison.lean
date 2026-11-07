/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic

/-!
# Comparing two nonnegative power estimates

The same quantity satisfies both estimates. A weighted geometric mean
retains the bad and incoherent gains together. This numerical helper
works directly in ENNReal, including zero, without finiteness premises.
-/

@[expose] public section
set_option autoImplicit false

open ENNReal

namespace WaveTurbulence.SumintPar

/-- Two power bounds imply their weighted geometric-mean power bound. -/
theorem ennreal_le_interpolated_power {X : ℝ≥0∞} {L a b t : ℝ} (hL : 0 < L)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (ha : X ≤ ENNReal.ofReal (L^a)) (hb : X ≤ ENNReal.ofReal (L^b)) :
    X ≤ ENNReal.ofReal (L^((1-t)*a+t*b)) := by
  have ht' : 0 ≤ 1-t := by linarith [ht.2]
  calc
    X = X^(1-t)*X^t := by
      rw [← ENNReal.rpow_add_of_nonneg (1-t) t ht' ht.1]
      simp only [sub_add_cancel,ENNReal.rpow_one]
    _ ≤ (ENNReal.ofReal (L^a))^(1-t)*(ENNReal.ofReal (L^b))^t :=
      mul_le_mul' (ENNReal.rpow_le_rpow ha ht') (ENNReal.rpow_le_rpow hb ht.1)
    _ = _ := by
      rw [ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hL a),
        ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hL b),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (Real.rpow_nonneg hL.le _) _),
        ← Real.rpow_mul hL.le,← Real.rpow_mul hL.le,← Real.rpow_add hL]
      congr 1
      ring

/-- A minimum envelope keeps one combined bound and a second factorwise bound simultaneously. -/
theorem mul_min_le_interpolated_power {F E : ℝ≥0∞} {L a b c t : ℝ} (hL : 0 < L)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hFE : F*E ≤ ENNReal.ofReal (L^a))
    (hF : F ≤ ENNReal.ofReal (L^b)) :
    F*min E (ENNReal.ofReal (L^c)) ≤ ENNReal.ofReal (L^((1-t)*a+t*(b+c))) := by
  have ha : F*min E (ENNReal.ofReal (L^c)) ≤ ENNReal.ofReal (L^a) :=
    (mul_le_mul' le_rfl (min_le_left _ _)).trans hFE
  have hb : F*min E (ENNReal.ofReal (L^c)) ≤ ENNReal.ofReal (L^(b+c)) := by
    calc
      _ ≤ ENNReal.ofReal (L^b)*ENNReal.ofReal (L^c) := mul_le_mul' hF (min_le_right _ _)
      _ = _ := by rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hL.le _),← Real.rpow_add hL]
  exact ennreal_le_interpolated_power hL ht ha hb

end WaveTurbulence.SumintPar
