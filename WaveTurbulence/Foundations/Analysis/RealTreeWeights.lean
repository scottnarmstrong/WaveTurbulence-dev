/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.TreeChoices

/-!
# Real-valued source resonance products

This is the same finite product as the extended-nonnegative-real envelope
weight, with explicit conversion for the final ordinary norm estimate.
-/

public section

namespace WaveTurbulence.Analysis.IntegrationTree

/-- Product of reciprocal Japanese brackets at branching vertices. -/
@[expose] noncomputable def realChoiceWeight (scale : ℝ) : (T : IntegrationTree) → T.Choice → ℝ
  | .leaf, _ => 1
  | .node a α σ₁ σ₂ σ₃ l m r, d =>
      oscillatoryWeight (scale * (node a α σ₁ σ₂ σ₃ l m r).choiceResonance d) *
        ((l.realChoiceWeight scale d.2.1.1 * m.realChoiceWeight scale d.2.1.2) *
          r.realChoiceWeight scale d.2.2)

theorem realChoiceWeight_nonneg (scale : ℝ) (T : IntegrationTree) (d : T.Choice) :
    0 ≤ T.realChoiceWeight scale d := by
  induction T with
  | leaf => exact zero_le_one
  | node a α σ₁ σ₂ σ₃ l m r hl hm hr =>
      exact mul_nonneg (oscillatoryWeight_pos _).le
        (mul_nonneg (mul_nonneg (hl _) (hm _)) (hr _))

theorem ofReal_realChoiceWeight (scale : ℝ) (T : IntegrationTree) (d : T.Choice) :
    ENNReal.ofReal (T.realChoiceWeight scale d) = T.choiceWeight scale d := by
  induction T with
  | leaf => exact ENNReal.ofReal_one
  | node a α σ₁ σ₂ σ₃ l m r hl hm hr =>
      change ENNReal.ofReal (oscillatoryWeight _ * ((_ * _) * _)) = _
      rw [ENNReal.ofReal_mul (oscillatoryWeight_pos _).le,
        ENNReal.ofReal_mul (mul_nonneg (realChoiceWeight_nonneg scale l _) (realChoiceWeight_nonneg scale m _)),
        ENNReal.ofReal_mul (realChoiceWeight_nonneg scale l _), hl, hm, hr]
      rfl

end WaveTurbulence.Analysis.IntegrationTree
