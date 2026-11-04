/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.ExponentPairSmoothing
public import WaveTurbulence.Foundations.Counting.LatticeDisc
public import WaveTurbulence.Foundations.Counting.LatticeBox
import Mathlib.Tactic

/-!
# Fractional smoothing of the actual outer circular caps

This conditional helper consumes only outer-cap frequency estimates, where
the endpoint square-root power profile applies. Vertical shifts are removed
by the exact unit-modulus phase identity, uniformly in the center.
-/

public section

namespace WaveTurbulence.Counting

/-- Outer-cap frequency estimates imply the exact circle transfer exponent
for their sawtooth sums, with no logarithmic or epsilon loss. -/
theorem circle_cap_sawtooth_le_of_frequency_scale {Q T c d C kappa lambda : ℝ}
    (hQ : 1 ≤ Q) (hC : 0 ≤ C) (hk : 0 < kappa) (hk1 : kappa < 1) (hl : lambda ≤ 1)
    (hfreq : ∀ n : ℕ, 0 < n →
      ‖∑ x ∈ (integerInterval (c-Q) (c+Q)).filter (fun x : ℤ => T < |(x:ℝ)-c|),
        NumberTheory.expPhase ((n:ℝ)*circleHeight Q c x)‖ ≤ (C*Q^lambda)*(n:ℝ)^kappa) :
    |∑ x ∈ (integerInterval (c-Q) (c+Q)).filter (fun x : ℤ => T < |(x:ℝ)-c|),
      NumberTheory.sawtooth (circleHeight Q c x+d)| ≤
      ((3:ℝ)/2+2*((Real.pi/kappa+1/(1-kappa))/Real.pi^2)*C)*
        Q^((kappa+lambda)/(1+kappa)) := by
  classical
  let s := (integerInterval (c-Q) (c+Q)).filter (fun x : ℤ => T < |(x:ℝ)-c|)
  have hcard : (s.card:ℝ) ≤ 3*Q := by
    have hs : (s.card:ℝ) ≤ ((integerInterval (c-Q) (c+Q)).card:ℝ) := by
      exact_mod_cast Finset.card_filter_le (integerInterval (c-Q) (c+Q)) _
    exact hs.trans ((card_integerInterval_le c (le_trans zero_le_one hQ)).trans
      (by linarith only [hQ]))
  apply NumberTheory.abs_sum_sawtooth_le_of_frequency_scale s
    (fun x : ℤ => circleHeight Q c x+d) hQ hC (by norm_num : (0:ℝ) ≤ 3)
    hk hk1 hl hcard
  intro n hn
  have he : ‖∑ x ∈ s, NumberTheory.expPhase ((n:ℝ)*(circleHeight Q c x+d))‖ =
      ‖∑ x ∈ s, NumberTheory.expPhase ((n:ℝ)*circleHeight Q c x)‖ := by
    simp_rw [mul_add,NumberTheory.expPhase_add]
    rw [← Finset.sum_mul,norm_mul,NumberTheory.norm_expPhase,mul_one]
  rw [he]
  exact hfreq n hn

end WaveTurbulence.Counting
