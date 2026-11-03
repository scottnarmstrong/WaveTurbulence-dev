/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.CircleOptimizedSource
public import WaveTurbulence.Foundations.NumberTheory.CircleShortSource
import Mathlib.Tactic

/-!
# Unconditional improved circle source estimate on integer windows

The large-frequency range uses the actual number of samples; short
windows use uniform curvature integrals; long windows use the optimized
shared B-process after the proved A estimate. All frequency and length
ranges are covered, including arbitrary real centers.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- Actual translated circle column estimate, uniformly for every integer
frequency at least one and every clipped outer-octant source window. -/
theorem norm_sum_circleColumnPhase_le_BScale {R h U c : ℝ}
    (hU : 1 ≤ U) (hUR : 3*U ≤ R) (hh : 1 ≤ h)
    {a b : ℕ} (hab : a ≤ b) (ha : R+c-2*U ≤ a) (hb : (b:ℝ) ≤ R+c-U)
    (haOct : R+c-R*(1-1/Real.sqrt 2) ≤ a) :
    ‖∑ n ∈ Finset.Ico a b, expPhase (VdCB.circleColumnPhase R h ((n:ℝ)+1-c))‖ ≤
      154618826665*VdCB.circleBScale R h U := by
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hR : 0 < R := (by positivity : 0 < 3*U).trans_le hUR
  have hhp : 0 < h := zero_lt_one.trans_le hh
  obtain ⟨hw,hUw⟩ := circle_source_frequency_regime hU hUR hh
  have hscale : 0 ≤ VdCB.circleBScale R h U := by unfold VdCB.circleBScale; positivity
  by_cases hwU : h*Real.sqrt R ≤ U^2
  · by_cases hshort : (b:ℝ)-a ≤ 2*stationaryBalancingRadius (h*Real.sqrt R) U
    · have he := norm_sum_circleColumnPhase_le_short_BScale hU hUR hhp hw hUw hwU hab ha hb hshort
      change ‖∑ n ∈ Finset.Ico a b, expPhase (VdCB.circleColumnPhase R h ((n:ℝ)+1-c))‖ ≤ _ at he
      change _ ≤ 154618826665*(h^((11:ℝ)/30)*R^((11:ℝ)/60)*U^((7:ℝ)/20))
      unfold VdCB.circleBScale at hscale
      linarith only [he,hscale]
    · apply norm_sum_circleColumnPhase_le_optimized_BScale hU hUR hhp hw hUw hwU hab ha hb haOct
      linarith only [hshort]
  · have hlarge : U^2 ≤ h*Real.sqrt R := le_of_not_ge hwU
    have htrivial : ‖∑ n ∈ Finset.Ico a b, expPhase (VdCB.circleColumnPhase R h ((n:ℝ)+1-c))‖ ≤ U := by
      calc
        _ ≤ ∑ n ∈ Finset.Ico a b, ‖expPhase (VdCB.circleColumnPhase R h ((n:ℝ)+1-c))‖ := norm_sum_le _ _
        _ = (b:ℝ)-a := by simp only [norm_expPhase,Finset.sum_const,nsmul_eq_mul,mul_one,Nat.card_Ico,Nat.cast_sub hab]
        _ ≤ _ := by linarith only [ha,hb]
    have hlocal := local_circle_scale_dominates_length hU (zero_lt_one.trans_le hw) hlarge
    rw [circle_source_local_power_identity hR hhp U] at hlocal
    change U ≤ VdCB.circleBScale R h U at hlocal
    exact htrivial.trans (hlocal.trans (by nlinarith only [hscale]))

end WaveTurbulence.NumberTheory
