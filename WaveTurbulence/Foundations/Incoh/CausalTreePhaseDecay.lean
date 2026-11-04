/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.CausalMixtureBound
public import WaveTurbulence.Foundations.Incoh.NormalizedLinkMixture

/-!
# Literal causal tree phase mixtures with incoherence decay

TARGET (incohproof28). All selected layer intervals and the causal ordering
are retained. The actual lattice coefficients and the remaining oscillatory
link amplitudes supply the mass bound; it is not a carrier field.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh

/-- The actual normalized link mixture against the fully causal selected-clock kernel. -/
@[expose] def treeCausalPhaseExtension {d n : ℕ} {V : Type*} (m : ℕ) (χ : ℝ → ℝ)
    (L γ δ : ℝ) (Q : V → Fin n → LayerLink d) (J : Finset (Fin n))
    (S : V → Set (Fin n → LinkMixturePoint d))
    (p : V → (Fin n → LinkMixturePoint d) → CausalBoxData m) (t : Fin 2 → ℝ) (v : V) : ℂ :=
  ∫ z, normalizedLinkMixtureAmplitude L γ δ (Q v) J (S v) z *
    universalCausalBoxKernel m χ t (p v z) ∂productLinkMixtureMeasure d n J

/-- A dimensional per-link constant and a cutoff-dependent prefactor control both tree cases. -/
theorem exists_treeCausalPhaseExtension_quarter_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ m : ℕ, ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n g k : ℕ, ∀ V : Type*,
        ∀ Q : V → Fin n → LayerLink d,
        (∀ v i, |((Q v i).leftLayer : ℝ) - (Q v i).rightLayer| + 1 ≤ D) →
        (∀ v, incoherenceCount (Q v) = g) → ∀ J : Finset (Fin n), J.card ≤ k →
        ∀ S : V → Set (Fin n → LinkMixturePoint d), (∀ v, MeasurableSet (S v)) →
        ∀ p : V → (Fin n → LinkMixturePoint d) → CausalBoxData m, (∀ v, Measurable (p v)) →
        Fourier.mixedFourierNorm00 (1 / 4) (treeCausalPhaseExtension m χ L γ δ Q J S p) ≤
          ENNReal.ofReal C * ENNReal.ofReal ((C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 2 * η) * g) * L ^ ((d : ℝ) * k)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_normalizedReplacedLinkMass_decay d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro m χ hχ hcχ
  obtain ⟨C, hC, hK⟩ := exists_universalCausalBoxKernel_bound m hχ hcχ
  obtain ⟨h⟩ := Fourier.exists_cutoffControl hχ hcχ
  refine ⟨C, hC, ?_⟩
  intro γ hγ η hη hηg δ hδ hδ₁ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ η hη hηg δ hδ hδ₁ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n g k V Q hspan hg J hJ S hS p hp
  let M := ENNReal.ofReal ((C₀ * δ) ^ n *
    L ^ (-(incoherenceExponent d γ - 2 * η) * g) * L ^ ((d : ℝ) * k))
  have hm (v : V) : (∫⁻ z, ‖normalizedLinkMixtureAmplitude L γ δ (Q v) J (S v) z‖ₑ
      ∂productLinkMixtureMeasure d n J) ≤ M := by
    apply (lintegral_normalizedLinkMixtureAmplitude_le (hL₀.trans hL) hδ γ (Q v) J (hS v)).trans
    simpa only [hg v] using hb L hL n (Q v) (hspan v) k J hJ
  have hs := mixedFourierNorm00_causalBox_mixture_le m hχ.continuous.measurable h
    (productLinkMixtureMeasure d n J) (fun v => normalizedLinkMixtureAmplitude L γ δ (Q v) J (S v)) p
    (fun v => integrable_normalizedLinkMixtureAmplitude (zero_lt_one.trans_le (hL₀.trans hL)) γ δ (Q v) J (hS v))
    (fun v => stronglyMeasurable_normalizedLinkMixtureAmplitude (zero_lt_one.trans_le (hL₀.trans hL)) γ δ (Q v) J (hS v)) hp hm
  exact hs.trans ((mul_le_mul' le_rfl hK).trans_eq (mul_comm M _))

end WaveTurbulence.Incoh
