/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.FeasibleTreeChoices
public import WaveTurbulence.Foundations.Analysis.RealTreeWeights

/-!
# Uniform frequency scaling on a ternary tree

All recursively accumulated resonances scale linearly with the vertex
frequencies. Endpoint choices and gap validity are unchanged.
-/

public section

namespace WaveTurbulence.Analysis.IntegrationTree

/-- Multiply every branching frequency by the same scalar. -/
@[expose] def scaleFrequency (c : ℝ) : IntegrationTree → IntegrationTree
  | .leaf => .leaf
  | .node a α σ₁ σ₂ σ₃ l m r => .node a (c * α) σ₁ σ₂ σ₃
      (l.scaleFrequency c) (m.scaleFrequency c) (r.scaleFrequency c)

theorem branchCount_scaleFrequency (c : ℝ) (T : IntegrationTree) :
    (T.scaleFrequency c).branchCount = T.branchCount := by
  induction T with
  | leaf => rfl
  | node a α σ₁ σ₂ σ₃ l m r hl hm hr => simp only [scaleFrequency, branchCount, hl, hm, hr]

private theorem scaleFrequency_eq_leaf_iff (c : ℝ) (T : IntegrationTree) :
    T.scaleFrequency c = .leaf ↔ T = .leaf := by cases T <;> simp [scaleFrequency]

theorem validGaps_scaleFrequency (c : ℝ) (T : IntegrationTree) (h : T.ValidGaps) :
    (T.scaleFrequency c).ValidGaps := by
  induction T with
  | leaf => trivial
  | node a α σ₁ σ₂ σ₃ l m r hl hm hr =>
      exact ⟨⟨h.1.1, fun he => h.1.2 ((scaleFrequency_eq_leaf_iff c l).mp he)⟩,
        ⟨h.2.1.1, fun he => h.2.1.2 ((scaleFrequency_eq_leaf_iff c m).mp he)⟩,
        ⟨h.2.2.1.1, fun he => h.2.2.1.2 ((scaleFrequency_eq_leaf_iff c r).mp he)⟩,
        hl h.2.2.2.1, hm h.2.2.2.2.1, hr h.2.2.2.2.2⟩

/-- Scaling frequencies preserves the binary endpoint choices. -/
@[expose] def scaleFrequencyChoiceEquiv (c : ℝ) : (T : IntegrationTree) → T.Choice ≃ (T.scaleFrequency c).Choice
  | .leaf => Equiv.refl Unit
  | .node _ _ _ _ _ l m r => Equiv.prodCongr (Equiv.refl Bool)
      (Equiv.prodCongr (Equiv.prodCongr (l.scaleFrequencyChoiceEquiv c) (m.scaleFrequencyChoiceEquiv c))
        (r.scaleFrequencyChoiceEquiv c))

theorem outputFrequency_scaleFrequency (c : ℝ) (T : IntegrationTree) (d : T.Choice) :
    (T.scaleFrequency c).outputFrequency (T.scaleFrequencyChoiceEquiv c d) = c * T.outputFrequency d := by
  induction T with
  | leaf => simp only [scaleFrequency, outputFrequency, mul_zero]
  | node a α σ₁ σ₂ σ₃ l m r hl hm hr =>
      change (if d.1 then (((l.scaleFrequency c).outputFrequency (l.scaleFrequencyChoiceEquiv c d.2.1.1) +
        (m.scaleFrequency c).outputFrequency (m.scaleFrequencyChoiceEquiv c d.2.1.2)) +
          (r.scaleFrequency c).outputFrequency (r.scaleFrequencyChoiceEquiv c d.2.2)) + c * α else 0) = _
      rw [hl, hm, hr]
      change (if d.1 then _ else 0) = c * (if d.1 then _ else 0)
      by_cases hd : d.1
      · erw [ite_eq_left hd, ite_eq_left hd]
        ring
      · erw [ite_eq_right hd, ite_eq_right hd, mul_zero]

theorem choiceResonance_scaleFrequency (c : ℝ) (T : IntegrationTree) (d : T.Choice) :
    (T.scaleFrequency c).choiceResonance (T.scaleFrequencyChoiceEquiv c d) = c * T.choiceResonance d := by
  cases T with
  | leaf => simp only [scaleFrequency, choiceResonance, mul_zero]
  | node a α σ₁ σ₂ σ₃ l m r =>
      change (((l.scaleFrequency c).outputFrequency (l.scaleFrequencyChoiceEquiv c d.2.1.1) +
        (m.scaleFrequency c).outputFrequency (m.scaleFrequencyChoiceEquiv c d.2.1.2)) +
          (r.scaleFrequency c).outputFrequency (r.scaleFrequencyChoiceEquiv c d.2.2)) + c * α = _
      rw [outputFrequency_scaleFrequency, outputFrequency_scaleFrequency, outputFrequency_scaleFrequency]
      change _ = c * ((l.outputFrequency _ + m.outputFrequency _) + r.outputFrequency _ + α)
      ring

theorem realChoiceWeight_scaleFrequency (c s : ℝ) (T : IntegrationTree) (d : T.Choice) :
    (T.scaleFrequency c).realChoiceWeight s (T.scaleFrequencyChoiceEquiv c d) = T.realChoiceWeight (s * c) d := by
  induction T with
  | leaf => rfl
  | node a α σ₁ σ₂ σ₃ l m r hl hm hr =>
      change oscillatoryWeight (s * ((node a α σ₁ σ₂ σ₃ l m r).scaleFrequency c).choiceResonance
        ((node a α σ₁ σ₂ σ₃ l m r).scaleFrequencyChoiceEquiv c d)) * _ = _
      rw [choiceResonance_scaleFrequency]
      change oscillatoryWeight (s * (c * (node a α σ₁ σ₂ σ₃ l m r).choiceResonance d)) *
        (((l.scaleFrequency c).realChoiceWeight s (l.scaleFrequencyChoiceEquiv c d.2.1.1) *
          (m.scaleFrequency c).realChoiceWeight s (m.scaleFrequencyChoiceEquiv c d.2.1.2)) *
            (r.scaleFrequency c).realChoiceWeight s (r.scaleFrequencyChoiceEquiv c d.2.2)) = _
      rw [hl, hm, hr, ← mul_assoc s c ((node a α σ₁ σ₂ σ₃ l m r).choiceResonance d)]
      rfl

end WaveTurbulence.Analysis.IntegrationTree
