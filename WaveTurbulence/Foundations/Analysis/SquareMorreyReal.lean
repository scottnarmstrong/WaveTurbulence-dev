/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.SquareMorreyPower

/-!
# Real integral formulation of TARGET (sobolev2)

The real exponent is `p = 2P`. The constants are independent of the function,
the point of evaluation and `M ≥ 1`.
-/

public section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
/-- For continuous functions on a compact set, the extended `p`-moment is
the coercion of the real integral. -/
theorem lintegral_enorm_rpow_eq_ofReal_integral {S : Set (Mom 2)} (hS : IsCompact S)
    {f : Mom 2 → F} (hf : Continuous f) {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ x in S, ‖f x‖ₑ ^ p) = ENNReal.ofReal (∫ x in S, ‖f x‖ ^ p) := by
  have hi := (hf.norm.rpow_const (fun _ => Or.inr hp)).continuousOn.integrableOn_compact (μ := volume) hS
  rw [ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _)]
  apply lintegral_congr
  intro x
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp]

/-- TARGET (sobolev2), L2330, with constants and range made explicit.
For `p = 2P`, the sufficient condition is `P ≥ 10001`. The derivative is
first order in the two variables, measured in operator norm. -/
theorem norm_rpow_le_square_morrey_largeParameter {f : Mom 2 → F}
    (hf : ContDiff ℝ 1 f) {x : Mom 2} (hx : x ∈ closedSquare 0 1)
    {p q : ℝ} (hpq : p.HolderConjugate q) (hp : 20002 ≤ p)
    {M : ℝ} (hM : 1 ≤ M) :
    ‖f x‖ ^ p ≤ (2 : ℝ) ^ p * M ^ (p / 200) * (∫ y in closedSquare 0 1, ‖f y‖ ^ p) +
      (2 * (squareMorreyConstant q).toReal) ^ p * M ^ (-50 * p) *
        (∫ z in closedSquare 0 1, ‖fderiv ℝ f z‖ ^ p) := by
  have hC := squareMorreyConstant_ne_top_of_holder hpq (by linarith only [hp])
  have hh := enorm_rpow_le_square_morrey_largeParameter hf hx hpq hp hM
  have hA : 0 ≤ ∫ y in closedSquare 0 1, ‖f y‖ ^ p :=
    integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
  have hB : 0 ≤ ∫ z in closedSquare 0 1, ‖fderiv ℝ f z‖ ^ p :=
    integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
  rw [lintegral_enorm_rpow_eq_ofReal_integral (isCompact_closedSquare 0 1)
      hf.continuous hpq.nonneg,
    lintegral_enorm_rpow_eq_ofReal_integral (isCompact_closedSquare 0 1)
      (hf.continuous_fderiv (by norm_num)) hpq.nonneg] at hh
  have hfin : (2 * squareMorreyConstant q) ^ p ≠ ⊤ := by
    apply ENNReal.rpow_ne_top_of_nonneg hpq.nonneg
    exact ENNReal.mul_ne_top (by norm_num) hC
  have ht := ENNReal.toReal_mono (by finiteness) hh
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at ht
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal hA, ENNReal.toReal_ofReal hB,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hM0 _),
    ← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)] using ht

end WaveTurbulence.Analysis
