/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.TreeIntegralBound
public import WaveTurbulence.Foundations.Analysis.TreeFrequencyScaling

/-!
# DH21 Lemma 10.2 in the paper's phase convention

`paperTimeIntegral` is the causal iterated integral with phase `πα`.
Its branch equation below exhibits the original integration bounds:
child `j` is evaluated at `s-σⱼ`, implementing the extra heap inequality
`t_child+σ_child < t_parent`. Leaves have value one and no time variable.
The integral ignores the auxiliary lower-endpoint labels, and source gaps
may be any nonnegative reals; the source range `[0,1]` is included.

The conclusion is the source's binary-choice resonance sum with a fixed
universal constant, for `0≤t≤1`. The purely combinatorial carrier is local;
a bridge to future frozen tree carriers remains a separate campaign task.
-/

public section

open MeasureTheory Set

namespace WaveTurbulence.Analysis.IntegrationTree

/-- The source iterated integral, with one phase `exp(π i α_v s)` per
branching vertex. Frequency scaling converts to the Fourier convention. -/
@[expose] noncomputable def paperTimeIntegral (T : IntegrationTree) (t : ℝ) : ℂ :=
  (T.scaleFrequency (1 / 2)).causalValue t

@[simp] theorem paperTimeIntegral_leaf (t : ℝ) : leaf.paperTimeIntegral t = 1 := rfl

/-- Complete branch equation for the source integral, including the
causal clipping required for empty gapped domains. -/
theorem paperTimeIntegral_node (a α σ₁ σ₂ σ₃ : ℝ) (l m r : IntegrationTree) (t : ℝ) :
    (node a α σ₁ σ₂ σ₃ l m r).paperTimeIntegral t =
      ∫ s in (0 : ℝ)..max 0 t, Complex.exp ((Real.pi * α * s : ℝ) * Complex.I) *
        ((l.paperTimeIntegral (s - σ₁) * m.paperTimeIntegral (s - σ₂)) * r.paperTimeIntegral (s - σ₃)) := by
  change (∫ s in (0 : ℝ)..max 0 t, timePhase ((1 / 2) * α) s *
    ((l.paperTimeIntegral (s - σ₁) * m.paperTimeIntegral (s - σ₂)) * r.paperTimeIntegral (s - σ₃))) = _
  have hphase (s : ℝ) : timePhase ((1 / 2) * α) s =
      Complex.exp ((Real.pi * α * s : ℝ) * Complex.I) := by
    unfold timePhase
    congr 1
    push_cast
    ring
  simp_rw [hphase]

/-- There are exactly `2^n` binary endpoint assignments. -/
theorem card_choice (T : IntegrationTree) : Fintype.card T.Choice = 2 ^ T.branchCount := by
  induction T with
  | leaf => change Fintype.card Unit = 2 ^ 0; norm_num
  | node a α σ₁ σ₂ σ₃ l m r hl hm hr =>
      change Fintype.card (Bool × ((l.Choice × m.Choice) × r.Choice)) = _
      rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, Fintype.card_bool, hl, hm, hr]
      simp only [branchCount, pow_add, pow_succ]
      ring

/-- DH21 Lemma 10.2: a universal exponential constant times the sum of
the products `∏_v ⟨q_v⟩⁻¹`, with precisely one binary choice at each
branch. Here `q_v=α_v+∑child d_child q_child`; `choiceResonance` and
`outputFrequency` give that recursion explicitly. No analytic result is
assumed in the hypotheses. -/
theorem norm_paperTimeIntegral_le (T : IntegrationTree) (h : T.ValidGaps)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖T.paperTimeIntegral t‖ ≤ timeIntegralConstant ^ T.branchCount * ∑ d, T.realChoiceWeight 1 d := by
  have hh := norm_causalValue_le_paper_choice_sum (T.scaleFrequency (1 / 2))
    (validGaps_scaleFrequency (1 / 2) T h) ht
  have hsum : (∑ d, (T.scaleFrequency (1 / 2)).realChoiceWeight 2 d) = ∑ d, T.realChoiceWeight 1 d := by
    rw [← (T.scaleFrequencyChoiceEquiv (1 / 2)).sum_comp]
    simp_rw [realChoiceWeight_scaleFrequency]
    norm_num
  rw [branchCount_scaleFrequency, hsum] at hh
  exact hh

/-- The universal constant is strictly positive and independent of the
tree, frequencies, gaps and external time. -/
theorem timeIntegralConstant_pos : 0 < timeIntegralConstant := by
  have hD := one_le_packetCostBase unitTimeCutoff
  unfold timeIntegralConstant treeIntegralConstant
  have hP : 0 < max (1 : ℝ) Real.pi := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  positivity

end WaveTurbulence.Analysis.IntegrationTree
