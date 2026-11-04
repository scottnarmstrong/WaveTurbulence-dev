/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.NormalizedLinkMixture
public import WaveTurbulence.Foundations.Incoh.RectangleMixtureBound

/-!
# Actual phase/internal-clock extensions for the two tree cases

TARGET (incohproof22)–(incohproof23), after phase expansion of the selected
root links. The amplitude consists of the literal normalized lattice factors;
no estimate is stored in these definitions.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The triangular tree extension formed from the literal link mixture. -/
@[expose] def treePhaseExtensionU {d n : ℕ} {V : Type*} (χ : ℝ → ℝ) (L γ δ : ℝ)
    (Q : V → Fin n → LayerLink d) (J : Finset (Fin n))
    (S : V → Set (Fin n → LinkMixturePoint d))
    (p : V → (Fin n → LinkMixturePoint d) → Mom 6) (t : Fin 2 → ℝ) (v : V) : ℂ :=
  ∫ z, normalizedLinkMixtureAmplitude L γ δ (Q v) J (S v) z * universalRectangleU χ t (p v z)
    ∂productLinkMixtureMeasure d n J

/-- The fourfold tree extension with the same literal amplitude. -/
@[expose] def treePhaseExtensionV {d n : ℕ} {V : Type*} (χ : ℝ → ℝ) (L γ δ : ℝ)
    (Q : V → Fin n → LayerLink d) (J : Finset (Fin n))
    (S : V → Set (Fin n → LinkMixturePoint d))
    (p : V → (Fin n → LinkMixturePoint d) → Mom 6) (t : Fin 2 → ℝ) (v : V) : ℂ :=
  ∫ z, normalizedLinkMixtureAmplitude L γ δ (Q v) J (S v) z * universalRectangleV χ t (p v z)
    ∂productLinkMixtureMeasure d n J

/-- The positive tree estimate in terms of the proved literal replacement mass. -/
theorem treePhaseExtensionU_norm_le {χ : ℝ → ℝ} (hχ : Measurable χ)
    (h : Fourier.CutoffControl χ) {d n : ℕ} {V : Type*} {L δ : ℝ}
    (hL : 1 ≤ L) (hδ : 0 < δ) (γ : ℝ) (Q : V → Fin n → LayerLink d) (J : Finset (Fin n))
    (S : V → Set (Fin n → LinkMixturePoint d)) (hS : ∀ v, MeasurableSet (S v))
    (p : V → (Fin n → LinkMixturePoint d) → Mom 6) (hp : ∀ v, Measurable (p v))
    {M : ℝ≥0∞} (hmass : ∀ v, normalizedReplacedLinkMass L γ δ (Q v) J ≤ M) :
    Fourier.mixedFourierNorm00 (1 / 4) (treePhaseExtensionU χ L γ δ Q J S p) ≤
      M * Fourier.mixedFourierNorm00 (1 / 4) (universalRectangleU χ) := by
  apply mixedFourierNorm00_rectangleU_mixture_le hχ h (productLinkMixtureMeasure d n J)
    (fun v => normalizedLinkMixtureAmplitude L γ δ (Q v) J (S v)) p
  · intro v
    exact integrable_normalizedLinkMixtureAmplitude (zero_lt_one.trans_le hL) γ δ (Q v) J (hS v)
  · intro v
    exact stronglyMeasurable_normalizedLinkMixtureAmplitude (zero_lt_one.trans_le hL) γ δ (Q v) J (hS v)
  · exact hp
  · intro v
    exact (lintegral_normalizedLinkMixtureAmplitude_le hL hδ γ (Q v) J (hS v)).trans (hmass v)

/-- The fourfold positive estimate pays the same replacement mass. -/
theorem treePhaseExtensionV_norm_le {χ : ℝ → ℝ} (hχ : Measurable χ)
    (h : Fourier.CutoffControl χ) {d n : ℕ} {V : Type*} {L δ : ℝ}
    (hL : 1 ≤ L) (hδ : 0 < δ) (γ : ℝ) (Q : V → Fin n → LayerLink d) (J : Finset (Fin n))
    (S : V → Set (Fin n → LinkMixturePoint d)) (hS : ∀ v, MeasurableSet (S v))
    (p : V → (Fin n → LinkMixturePoint d) → Mom 6) (hp : ∀ v, Measurable (p v))
    {M : ℝ≥0∞} (hmass : ∀ v, normalizedReplacedLinkMass L γ δ (Q v) J ≤ M) :
    Fourier.mixedFourierNorm00 (1 / 4) (treePhaseExtensionV χ L γ δ Q J S p) ≤
      M * Fourier.mixedFourierNorm00 (1 / 4) (universalRectangleV χ) := by
  apply mixedFourierNorm00_rectangleV_mixture_le hχ h (productLinkMixtureMeasure d n J)
    (fun v => normalizedLinkMixtureAmplitude L γ δ (Q v) J (S v)) p
  · intro v
    exact integrable_normalizedLinkMixtureAmplitude (zero_lt_one.trans_le hL) γ δ (Q v) J (hS v)
  · intro v
    exact stronglyMeasurable_normalizedLinkMixtureAmplitude (zero_lt_one.trans_le hL) γ δ (Q v) J (hS v)
  · exact hp
  · intro v
    exact (lintegral_normalizedLinkMixtureAmplitude_le hL hδ γ (Q v) J (hS v)).trans (hmass v)

end WaveTurbulence.Incoh
