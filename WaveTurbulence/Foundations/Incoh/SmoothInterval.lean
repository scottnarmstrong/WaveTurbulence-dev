/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Smooth interval windows for the tree time-order fibers

TARGET (incohproof27)–(incohproof28): the literal time domain has interval
boundaries. These windows preserve positivity and have bounded support;
they will approximate those boundaries before applying the smooth phase lemma.
-/

public section
noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace WaveTurbulence.Incoh

/-- A smoothed indicator of `(a,b]`, with transition width `ε`. -/
@[expose] def smoothInterval (ε a b t : ℝ) : ℝ :=
  Real.smoothTransition ((t - a) / ε) - Real.smoothTransition ((t - b) / ε)

@[fun_prop] theorem contDiff_smoothInterval (ε a b : ℝ) :
    ContDiff ℝ ∞ (smoothInterval ε a b) := by
  unfold smoothInterval
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).sub
    (Real.smoothTransition.contDiff.comp (by fun_prop))

theorem smoothInterval_nonneg {ε a b : ℝ} (hε : 0 < ε) (hab : a ≤ b) (t : ℝ) :
    0 ≤ smoothInterval ε a b t := by
  apply sub_nonneg.mpr
  apply Real.smoothTransition.monotone
  exact div_le_div_of_nonneg_right (by linarith) hε.le

theorem smoothInterval_le_one (ε a b t : ℝ) : smoothInterval ε a b t ≤ 1 := by
  exact (sub_le_self _ (Real.smoothTransition.nonneg _)).trans
    (Real.smoothTransition.le_one _)

theorem smoothInterval_eq_zero_of_le {ε a b t : ℝ} (hε : 0 < ε)
    (hab : a ≤ b) (ht : t ≤ a) : smoothInterval ε a b t = 0 := by
  have hta : (t - a) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  have htb : (t - b) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  simp only [smoothInterval, Real.smoothTransition.zero_of_nonpos hta,
    Real.smoothTransition.zero_of_nonpos htb, sub_self]

theorem smoothInterval_eq_zero_of_ge {ε a b t : ℝ} (hε : 0 < ε)
    (hab : a ≤ b) (ht : b + ε ≤ t) : smoothInterval ε a b t = 0 := by
  have hta : 1 ≤ (t - a) / ε := (le_div_iff₀ hε).mpr (by linarith)
  have htb : 1 ≤ (t - b) / ε := (le_div_iff₀ hε).mpr (by linarith)
  simp only [smoothInterval, Real.smoothTransition.one_of_one_le hta,
    Real.smoothTransition.one_of_one_le htb, sub_self]

theorem hasCompactSupport_smoothInterval {ε a b : ℝ} (hε : 0 < ε) (hab : a ≤ b) :
    HasCompactSupport (smoothInterval ε a b) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := a) (b := b + ε))
  intro t ht
  rcases not_and_or.mp ht with ha | hb
  · exact smoothInterval_eq_zero_of_le hε hab (le_of_not_ge ha)
  · exact smoothInterval_eq_zero_of_ge hε hab (le_of_not_ge hb)

theorem smoothInterval_eq_one {ε a b t : ℝ} (hε : 0 < ε)
    (ha : a + ε ≤ t) (hb : t ≤ b) : smoothInterval ε a b t = 1 := by
  have hta : 1 ≤ (t - a) / ε := (le_div_iff₀ hε).mpr (by linarith)
  have htb : (t - b) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  simp only [smoothInterval, Real.smoothTransition.one_of_one_le hta,
    Real.smoothTransition.zero_of_nonpos htb, sub_zero]

end WaveTurbulence.Incoh
