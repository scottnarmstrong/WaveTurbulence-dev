/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.TreeResonanceWeights

/-!
# Cutoff-independent binary choices and resonance products

These finite carriers and their frequencies depend only on the labelled
ternary tree, not on the cutoff or feasible endpoints. They identify the
constructed packet bound with the source sum over all binary vertex choices.
-/

public section

open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Analysis.IntegrationTree

/-- One binary endpoint choice at each branching vertex. -/
@[expose] def Choice : IntegrationTree → Type
  | .leaf => Unit
  | .node _ _ _ _ _ l m r => Bool × ((l.Choice × m.Choice) × r.Choice)

noncomputable instance fintypeChoice (T : IntegrationTree) : Fintype T.Choice := by
  induction T with
  | leaf => exact inferInstanceAs (Fintype Unit)
  | node a α σ₁ σ₂ σ₃ l m r hl hm hr =>
      letI := hl
      letI := hm
      letI := hr
      exact inferInstanceAs (Fintype (Bool × ((l.Choice × m.Choice) × r.Choice)))

/-- Frequency contributed by a subtree after its endpoint choice. -/
@[expose] def outputFrequency : (T : IntegrationTree) → T.Choice → ℝ
  | .leaf, _ => 0
  | .node _ α _ _ _ l m r, d =>
      if d.1 then ((l.outputFrequency d.2.1.1 + m.outputFrequency d.2.1.2) +
        r.outputFrequency d.2.2) + α else 0

/-- The vertex resonance is its own frequency plus the frequencies
contributed by its three children. -/
@[expose] def choiceResonance : (T : IntegrationTree) → T.Choice → ℝ
  | .leaf, _ => 0
  | .node _ α _ _ _ l m r, d =>
      ((l.outputFrequency d.2.1.1 + m.outputFrequency d.2.1.2) + r.outputFrequency d.2.2) + α

/-- The product of Japanese-bracket reciprocals at all branching vertices. -/
@[expose] noncomputable def choiceWeight (scale : ℝ) : (T : IntegrationTree) → T.Choice → ℝ≥0∞
  | .leaf, _ => 1
  | .node a α σ₁ σ₂ σ₃ l m r, d =>
      ENNReal.ofReal (oscillatoryWeight (scale * (node a α σ₁ σ₂ σ₃ l m r).choiceResonance d)) *
        ((l.choiceWeight scale d.2.1.1 * m.choiceWeight scale d.2.1.2) * r.choiceWeight scale d.2.2)

/-- The analytic packet carrier is precisely the binary-choice carrier. -/
@[expose] noncomputable def choiceEquiv {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) : (T : IntegrationTree) → (h : T.Admissible) →
      T.Choice ≃ (T.packet hχ hs h).Index
  | .leaf, _ => Equiv.refl Unit
  | .node _ _ _ _ _ l m r, h => Equiv.prodCongr (Equiv.refl Bool)
      (Equiv.prodCongr (Equiv.prodCongr (l.choiceEquiv hχ hs h.2.1)
        (m.choiceEquiv hχ hs h.2.2.1)) (r.choiceEquiv hχ hs h.2.2.2))

/-- The constructed packet centres are the source output frequencies. -/
theorem centre_choiceEquiv {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) (T : IntegrationTree) (h : T.Admissible) (d : T.Choice) :
    (T.packet hχ hs h).centre (T.choiceEquiv hχ hs h d) = T.outputFrequency d := by
  induction T with
  | leaf => rfl
  | node a α σ₁ σ₂ σ₃ l m r hl hm hr =>
      change (if d.1 then (((l.packet hχ hs h.2.1).centre (l.choiceEquiv hχ hs h.2.1 d.2.1.1) +
        (m.packet hχ hs h.2.2.1).centre (m.choiceEquiv hχ hs h.2.2.1 d.2.1.2)) +
          (r.packet hχ hs h.2.2.2).centre (r.choiceEquiv hχ hs h.2.2.2 d.2.2)) + α else 0) = _
      erw [hl h.2.1, hm h.2.2.1, hr h.2.2.2]
      rfl

/-- The denominator product is unchanged under the carrier equivalence. -/
theorem resonanceWeight_choiceEquiv {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) (scale : ℝ) (T : IntegrationTree) (h : T.Admissible) (d : T.Choice) :
    T.resonanceWeight hχ hs scale h (T.choiceEquiv hχ hs h d) = T.choiceWeight scale d := by
  induction T with
  | leaf => rfl
  | node a α σ₁ σ₂ σ₃ l m r hl hm hr =>
      change ENNReal.ofReal (oscillatoryWeight (scale *
        ((((l.packet hχ hs h.2.1).centre (l.choiceEquiv hχ hs h.2.1 d.2.1.1) +
          (m.packet hχ hs h.2.2.1).centre (m.choiceEquiv hχ hs h.2.2.1 d.2.1.2)) +
            (r.packet hχ hs h.2.2.2).centre (r.choiceEquiv hχ hs h.2.2.2 d.2.2)) + α))) *
        ((l.resonanceWeight hχ hs scale h.2.1 (l.choiceEquiv hχ hs h.2.1 d.2.1.1) *
          m.resonanceWeight hχ hs scale h.2.2.1 (m.choiceEquiv hχ hs h.2.2.1 d.2.1.2)) *
            r.resonanceWeight hχ hs scale h.2.2.2 (r.choiceEquiv hχ hs h.2.2.2 d.2.2)) = _
      erw [centre_choiceEquiv hχ hs l h.2.1, centre_choiceEquiv hχ hs m h.2.2.1,
        centre_choiceEquiv hχ hs r h.2.2.2, hl h.2.1, hm h.2.2.1, hr h.2.2.2]
      rfl

end WaveTurbulence.Analysis.IntegrationTree
