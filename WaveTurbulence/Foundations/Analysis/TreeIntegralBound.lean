/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.TreePacketCost
public import WaveTurbulence.Foundations.Analysis.FrequencyScale
public import WaveTurbulence.Foundations.Analysis.FeasibleTreeChoices
public import WaveTurbulence.Foundations.Analysis.RealTreeWeights
public import WaveTurbulence.Foundations.Analysis.UnitTimeCutoff

/-!
# The oscillatory ternary-tree time-integral estimate

The actual causal iterated integral is controlled by the sum over one
binary choice per branching vertex of the product of reciprocal resonance
brackets. Gaps are nonnegative, leaf gaps are zero, and the external time
is in `[0,1]`. The construction proves every spectral input to the estimate.
-/

public section

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.Analysis.IntegrationTree

/-- The cutoff analytic integral satisfies the source choice sum, with
all common costs displayed. -/
theorem enorm_value_le_choice_sum {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) (T : IntegrationTree) (h : T.Admissible) (t : ℝ) :
    ‖T.value χ t‖ₑ ≤ T.packetCost χ * ENNReal.ofReal Real.pi * ∑ d, T.choiceWeight 1 d := by
  have hh := enorm_value_le_resonance_sum hχ hs T h t
  rw [← (T.choiceEquiv hχ hs h).sum_comp (T.resonanceWeight hχ hs 1 h)] at hh
  simp_rw [resonanceWeight_choiceEquiv] at hh
  convert hh using 1
  ring

/-- The full causal estimate, first in the Fourier frequency normalization. -/
theorem enorm_causalValue_le_choice_sum {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) (hχone : ∀ t ∈ Icc (0 : ℝ) 1, χ t = 1)
    (T : IntegrationTree) (h : T.ValidGaps) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖T.causalValue t‖ₑ ≤ ENNReal.ofReal (treeIntegralConstant χ) ^ T.branchCount *
      ∑ d, T.choiceWeight 1 d := by
  cases T with
  | leaf =>
      change ‖(1 : ℂ)‖ₑ ≤ ENNReal.ofReal (treeIntegralConstant χ) ^ 0 * ∑ _ : Unit, (1 : ℝ≥0∞)
      simp only [enorm_one, pow_zero, Fintype.sum_unique, one_mul, le_refl]
  | node a α σ₁ σ₂ σ₃ l m r =>
      let T := node a α σ₁ σ₂ σ₃ l m r
      by_cases hf : T.threshold ≤ t
      · have had := admissible_withThresholds T h (hf.trans ht.2)
        rw [causalValue_eq_value_withThresholds hχone T h ⟨hf, ht.2⟩]
        have hh := enorm_value_le_choice_sum hχ hs T.withThresholds had t
        have hn : 0 < T.withThresholds.branchCount := by
          rw [branchCount_withThresholds]
          change 0 < l.branchCount + m.branchCount + r.branchCount + 1
          omega
        have hcost := packetCost_mul_pi_le_pow χ T.withThresholds hn
        refine hh.trans ?_
        have hsum : (∑ d, T.withThresholds.choiceWeight 1 d) = ∑ d, T.choiceWeight 1 d := by
          rw [← T.withThresholdsChoiceEquiv.sum_comp]
          simp_rw [choiceWeight_withThresholds]
        rw [hsum, ← branchCount_withThresholds T]
        exact mul_le_mul' hcost le_rfl
      · have hz := causalValue_eq_zero_of_le_threshold T h
          (by change node a α σ₁ σ₂ σ₃ l m r ≠ leaf; intro hh; cases hh) t (le_of_not_ge hf)
        rw [hz, enorm_zero]
        exact zero_le

/-- Conversion to the paper frequency normalization, still with an
extended-nonnegative-real norm for convenient finite-sum arithmetic. -/
theorem enorm_causalValue_le_paper_choice_sum {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) (hχone : ∀ t ∈ Icc (0 : ℝ) 1, χ t = 1)
    (T : IntegrationTree) (h : T.ValidGaps) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖T.causalValue t‖ₑ ≤ (2 * ENNReal.ofReal (treeIntegralConstant χ)) ^ T.branchCount *
      ∑ d, T.choiceWeight 2 d := by
  have hh := enorm_causalValue_le_choice_sum hχ hs hχone T h ht
  have hsum : (∑ d, T.choiceWeight 1 d) ≤ (2 : ℝ≥0∞) ^ T.branchCount * ∑ d, T.choiceWeight 2 d := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun d _ => choiceWeight_one_le_two T d
  refine hh.trans ((mul_le_mul' le_rfl hsum).trans_eq ?_)
  rw [mul_pow]
  ring

/-- Universal constant in the local DH21 ternary-tree estimate. -/
@[expose] noncomputable def timeIntegralConstant : ℝ := 2 * treeIntegralConstant unitTimeCutoff

/-- DH21 Lemma 10.2 for the local recursive ternary-tree carrier. The
phase at a vertex is `2π i α_v s`; accordingly the paper resonance at
that vertex is `2 * choiceResonance`. The choice weight is exactly the
product of `⟨q_v⟩⁻¹` over branching vertices. -/
theorem norm_causalValue_le_paper_choice_sum (T : IntegrationTree) (h : T.ValidGaps)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖T.causalValue t‖ ≤ timeIntegralConstant ^ T.branchCount * ∑ d, T.realChoiceWeight 2 d := by
  have hC : 0 ≤ treeIntegralConstant unitTimeCutoff := by
    unfold treeIntegralConstant
    positivity
  have hrhs : 0 ≤ timeIntegralConstant ^ T.branchCount * ∑ d, T.realChoiceWeight 2 d :=
    mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) hC) _) (Finset.sum_nonneg fun d _ => realChoiceWeight_nonneg 2 T d)
  apply (ENNReal.ofReal_le_ofReal_iff hrhs).mp
  have hh := enorm_causalValue_le_paper_choice_sum contDiff_unitTimeCutoff hasCompactSupport_unitTimeCutoff
    (fun t ht => unitTimeCutoff_eq_one ht) T h ht
  unfold timeIntegralConstant
  rw [ENNReal.ofReal_mul (pow_nonneg (mul_nonneg (by norm_num) hC) _),
    ENNReal.ofReal_pow (mul_nonneg (by norm_num) hC),
    ENNReal.ofReal_sum_of_nonneg (fun d _ => realChoiceWeight_nonneg 2 T d)]
  simp_rw [ofReal_realChoiceWeight]
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  simpa only [ofReal_norm] using hh

end WaveTurbulence.Analysis.IntegrationTree
