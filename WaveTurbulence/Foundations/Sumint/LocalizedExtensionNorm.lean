/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.LocalizedExtensionFourier

/-!
# The exact localized ambient extension retains the normalized coefficient mass

Spatial recombination keeps the same output supremum and introduces no
output cardinality factor beyond the already proved positive endpoint.
-/

public section
open MeasureTheory
open scoped ENNReal
namespace WaveTurbulence.Sumint

/-- Conditional linear recombination estimate for the actual localized source extension. -/
theorem XNorm00_localizedSourceExtension_le {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    (hI : 0 < D.S.I) (N : ℕ) (h : ℝ) {A L γ δ η : ℝ} {Dsteps : ℕ}
    (hL : 0 < L) (hη : η ≤ 1/3) (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) (p : D.S.VIdx → Fin d → ℝ)
    {V : Type*} [Countable V] (E : V → Fin 4 → Mom d) (θ : ℝ) (B : ℝ≥0∞)
    (hF : ∀ ν : D.S.VIdx → Mom d,
      XNorm00 θ (fun t v => weightedSourceExtension D hI N h L γ δ η p ν (E v 0-E v 1) t) ≤ B) :
    XNorm00 θ (fun t v => localizedSourceExtension D hI N h L γ δ η a b p (E v) t) ≤
      (∫⁻ ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d, ‖normalizedSourceCoefficient D L γ η a b ξ‖ₑ)*B := by
  exact XNorm00_integral_weightedSourceExtension_le D hI N h hL γ δ η hη p _
    (continuous_sourceInputModulation D).measurable (fun v => E v 0-E v 1)
    (normalizedSourceCoefficient D L γ η a b)
    (continuous_normalizedSourceCoefficient hd D hD a b).measurable
    (integrable_normalizedSourceCoefficient hd D hL hD a b) _
    (fun v => (continuous_sourceExternalCharacter D (E v)).measurable)
    (fun ξ v => (norm_source_external_character D ξ (E v)).le) θ B (fun ξ => hF _)

end WaveTurbulence.Sumint
