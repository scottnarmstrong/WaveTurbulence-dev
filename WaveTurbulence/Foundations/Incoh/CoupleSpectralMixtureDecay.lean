/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.CoupleExtensionAgreement
public import WaveTurbulence.Foundations.Incoh.DominatedFourierMixture

/-!
# Spectral mixtures of the literal localized couple kernels

TARGET Step (2) to (incohproof20). A pointwise amplitude envelope permits
Tonelli after the momentum supremum. The scalar kernel estimates are
proved by the analytic core, not assumed as carrier fields.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Conditional transport through an actual Fourier mixture, with literal couple kernels. -/
theorem exists_coupleSpectralMixture_bound (d : ℕ) (hd : 3 ≤ d)
    (η : ℝ) (hη : 0 < η) (hη₁ : η ≤ 1 / 3) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n g : ℕ, 1 ≤ g →
        ∀ U V : Type*, ∀ (_ : MeasurableSpace U), ∀ μ : Measure U, SFinite μ →
        ∀ Q : U → Fin n → LayerLink d,
        (∀ u, incoherenceCount (Q u) = g) →
        (∀ u i, |((Q u i).leftLayer : ℝ) - (Q u i).rightLayer| + 1 ≤ D) →
        ∀ I : U → Set (Fin n → Fin 2 → ℝ), (∀ u, MeasurableSet (I u)) →
        (∀ u, I u ⊆ univ.pi (fun i => linkBox (Q u i))) → ∀ R : RootCoordinates n,
        ∀ A : V → U → ℂ, ∀ E : U → ℝ≥0∞, Measurable E → (∀ v u, ‖A v u‖ₑ ≤ E u) →
        StronglyMeasurable (fun z : (Fin 2 → ℝ) × U =>
          R.coupleExtension rootCutoff L γ δ (Q z.2) (I z.2) z.1) →
        (∀ v, Integrable (fun z : (Fin 2 → ℝ) × U => A v z.2 *
          R.coupleExtension rootCutoff L γ δ (Q z.2) (I z.2) z.1) (volume.prod μ)) →
        Fourier.mixedFourierNorm00 η
          (fun t v => ∫ u, A v u * R.coupleExtension rootCutoff L γ δ (Q u) (I u) t ∂μ) ≤
          (∫⁻ u, E u ∂μ) * ENNReal.ofReal ((C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * g)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_coupleExtension_timeFourier_bound d hd η hη hη₁
    contDiff_rootCutoff hasCompactSupport_rootCutoff
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ hηγ δ hδ hδ₁ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n g hg U V _ μ hμ Q hcount hspan I hI hbox R A E hE hA hK hjoint
  let _ : SFinite μ := hμ
  have hnorm (u : U) : Fourier.timeFourierNorm η
      (R.coupleExtension rootCutoff L γ δ (Q u) (I u)) ≤
      ENNReal.ofReal ((C₀ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * g)) := by
    simpa only [hcount u] using hb L hL n (Q u) (by simpa only [hcount u] using hg)
      (hspan u) (I u) (hI u) (hbox u) R
  have hiK (u : U) : Integrable (R.coupleExtension rootCutoff L γ δ (Q u) (I u)) :=
    Fourier.integrable_of_timeFourierNorm_lt_top (lt_of_le_of_lt (hnorm u) ENNReal.ofReal_lt_top)
  apply (mixedFourierNorm00_integral_dominated_le μ η A
    (fun t u => R.coupleExtension rootCutoff L γ δ (Q u) (I u) t) hK hiK hjoint hE hA).trans
  calc
    _ ≤ ∫⁻ u, E u * ENNReal.ofReal ((C₀ * δ) ^ n *
        L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * g)) ∂μ :=
      lintegral_mono (fun u => mul_le_mul' le_rfl (hnorm u))
    _ = _ := lintegral_mul_const _ hE

end WaveTurbulence.Incoh
