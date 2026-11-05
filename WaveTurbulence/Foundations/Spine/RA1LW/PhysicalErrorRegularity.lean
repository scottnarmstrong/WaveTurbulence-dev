/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.PhysicalErrorScalar

/-! # Actual combined scalar source error retains joint measurability -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh ClassJR

/-- Joint scalar measurability follows from the actual half-cell NT
remainder and Wick profiles, with their original finite source weights. -/
theorem stronglyMeasurable_physicalErrorScalar_joint {d : ℕ} (hd : 3 ≤ d)
    (Q : RegCpl) (hn : 0 < Q.links.length) {L : ℝ} (hL : 0 < L) (δ γ : ℝ) (ζ : ℂ)
    (C : (Z : (chosenSet Q.links).powerset) →
      ({j : Fin Q.links.length // j ∉ markedLinkIndices Q Z.val} → ℝ) → ℝ × ℝ → ℂ)
    (hC : ∀ Z, StronglyMeasurable (Function.uncurry (C Z)))
    (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ) :
    StronglyMeasurable (fun p : (ℝ × ℝ) ×
      ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d)) =>
        physicalErrorScalar L δ γ Q ζ C p.1 p.2.1 p.2.2 z) := by
  classical
  unfold physicalErrorScalar
  apply StronglyMeasurable.const_mul
  apply Finset.stronglyMeasurable_fun_sum
  intro Z _
  exact ((stronglyMeasurable_localRemainder_joint hd hn L (2*δ) γ (markedLinkIndices Q Z.val)
      (hC Z) z).add
    (stronglyMeasurable_normalizedWickCorrection_joint hL (2*δ) γ z (markedLinkIndices Q Z.val) (hC Z))).const_mul _

end WaveTurbulence.RA1Leafwise
