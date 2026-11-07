/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceModulationRegularity
public import WaveTurbulence.Foundations.SumintPar.LocalizedSpatialExpansion

/-!
# Exact inversion of the normalized spatial coefficient

The normalization is the real inverse of the weight decay already
included in the kernel input. The coefficient identity counts it once.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory
namespace WaveTurbulence.SumintPar

/-- Fourier inversion of the normalized coefficient with both literal affine characters. -/
theorem normalized_source_coefficient_expansion {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    {A L γ η : ℝ} {N : ℕ} (hL : 0 < L) (hD : D.Admissible A L γ η N)
    (a b : D.S.VIdx → Fin d → ℤ) (x : D.S.VIdx → Fin d → ℤ) (E : Fin 4 → Mom d) :
    (∫ ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d,
      normalizedSourceCoefficient D L γ η a b (E 0 - E 1) ξ *
        (Real.fourierChar (externalModulation D (fun v => ξ (.inl v)) (fun v => ξ (.inr v)) E):ℂ) *
        inputCharacter D L (inputModulation D (fun v => ξ (.inl v)) (fun v => ξ (.inr v))) x) =
      (((sourceWeightDecay D L γ η)⁻¹:ℝ):ℂ)*localizedSourceWeight D L a b E x := by
  have he : (fun ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d =>
      normalizedSourceCoefficient D L γ η a b (E 0 - E 1) ξ *
        (Real.fourierChar (externalModulation D (fun v => ξ (.inl v)) (fun v => ξ (.inr v)) E):ℂ) *
        inputCharacter D L (inputModulation D (fun v => ξ (.inl v)) (fun v => ξ (.inr v))) x) =
      fun ξ => (((sourceWeightDecay D L γ η)⁻¹:ℝ):ℂ)*
        (tensorCharacter (Sum.elim (D.kVec L x E) (D.ℓVec L x E)) ξ * sourceCoefficient D a b (E 0 - E 1) ξ) := by
    funext ξ
    unfold tensorCharacter
    rw [source_affine_character_eq]
    unfold normalizedSourceCoefficient
    ring
  rw [he,integral_const_mul,source_coefficient_expansion hd D hL hD a b x E]
  rfl

/-- The same actual normalized, affine-modulated coefficient is genuinely integrable. -/
theorem integrable_normalized_source_modulatedCoefficient {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    {A L γ η : ℝ} {N : ℕ} (hL : 0 < L) (hD : D.Admissible A L γ η N)
    (a b : D.S.VIdx → Fin d → ℤ) (x : D.S.VIdx → Fin d → ℤ) (E : Fin 4 → Mom d) :
    Integrable (fun ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d =>
      normalizedSourceCoefficient D L γ η a b (E 0 - E 1) ξ *
        (Real.fourierChar (externalModulation D (fun v => ξ (.inl v)) (fun v => ξ (.inr v)) E):ℂ) *
        inputCharacter D L (inputModulation D (fun v => ξ (.inl v)) (fun v => ξ (.inr v))) x) := by
  have hi := (integrable_normalizedSourceCoefficient hd D hL hD a b (E 0 - E 1)).mul_bdd
    (continuous_sourceExternalCharacter D E).measurable.aestronglyMeasurable
    (ae_of_all _ (fun ξ => (norm_source_external_character D ξ E).le))
  exact hi.mul_bdd
    ((continuous_inputCharacter D L x).comp (continuous_sourceInputModulation D)).measurable.aestronglyMeasurable
    (ae_of_all _ (fun ξ => (norm_inputCharacter D L _ x).le))

end WaveTurbulence.SumintPar
