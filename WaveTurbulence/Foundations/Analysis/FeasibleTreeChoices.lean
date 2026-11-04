/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.FeasibleIntegrationTree
public import WaveTurbulence.Foundations.Analysis.TreeChoices

/-!
# Feasible endpoints preserve all binary resonance data

Replacing lower endpoints does not change the branching count, binary
choices, output frequencies or resonance weights.
-/

public section

namespace WaveTurbulence.Analysis.IntegrationTree

/-- Threshold replacement changes no branching vertices. -/
theorem branchCount_withThresholds (T : IntegrationTree) :
    T.withThresholds.branchCount = T.branchCount := by
  induction T with
  | leaf => rfl
  | node a α σ₁ σ₂ σ₃ l m r hl hm hr =>
      simp only [withThresholds, branchCount, hl, hm, hr]

/-- Canonical identification of binary choices before and after endpoint replacement. -/
@[expose] def withThresholdsChoiceEquiv : (T : IntegrationTree) → T.Choice ≃ T.withThresholds.Choice
  | .leaf => Equiv.refl Unit
  | .node _ _ _ _ _ l m r => Equiv.prodCongr (Equiv.refl Bool)
      (Equiv.prodCongr (Equiv.prodCongr l.withThresholdsChoiceEquiv m.withThresholdsChoiceEquiv)
        r.withThresholdsChoiceEquiv)

theorem outputFrequency_withThresholds (T : IntegrationTree) (d : T.Choice) :
    T.withThresholds.outputFrequency (T.withThresholdsChoiceEquiv d) = T.outputFrequency d := by
  induction T with
  | leaf => rfl
  | node a α σ₁ σ₂ σ₃ l m r hl hm hr =>
      change (if d.1 then ((l.withThresholds.outputFrequency (l.withThresholdsChoiceEquiv d.2.1.1) +
        m.withThresholds.outputFrequency (m.withThresholdsChoiceEquiv d.2.1.2)) +
          r.withThresholds.outputFrequency (r.withThresholdsChoiceEquiv d.2.2)) + α else 0) = _
      rw [hl, hm, hr]
      rfl

theorem choiceResonance_withThresholds (T : IntegrationTree) (d : T.Choice) :
    T.withThresholds.choiceResonance (T.withThresholdsChoiceEquiv d) = T.choiceResonance d := by
  cases T with
  | leaf => rfl
  | node a α σ₁ σ₂ σ₃ l m r =>
      change ((l.withThresholds.outputFrequency (l.withThresholdsChoiceEquiv d.2.1.1) +
        m.withThresholds.outputFrequency (m.withThresholdsChoiceEquiv d.2.1.2)) +
          r.withThresholds.outputFrequency (r.withThresholdsChoiceEquiv d.2.2)) + α = _
      rw [outputFrequency_withThresholds, outputFrequency_withThresholds, outputFrequency_withThresholds]
      rfl

theorem choiceWeight_withThresholds (scale : ℝ) (T : IntegrationTree) (d : T.Choice) :
    T.withThresholds.choiceWeight scale (T.withThresholdsChoiceEquiv d) = T.choiceWeight scale d := by
  induction T with
  | leaf => rfl
  | node a α σ₁ σ₂ σ₃ l m r hl hm hr =>
      change ENNReal.ofReal (oscillatoryWeight (scale *
        (node a α σ₁ σ₂ σ₃ l m r).withThresholds.choiceResonance
          ((node a α σ₁ σ₂ σ₃ l m r).withThresholdsChoiceEquiv d))) *
        ((l.withThresholds.choiceWeight scale (l.withThresholdsChoiceEquiv d.2.1.1) *
          m.withThresholds.choiceWeight scale (m.withThresholdsChoiceEquiv d.2.1.2)) *
            r.withThresholds.choiceWeight scale (r.withThresholdsChoiceEquiv d.2.2)) = _
      rw [choiceResonance_withThresholds, hl, hm, hr]
      rfl

end WaveTurbulence.Analysis.IntegrationTree
