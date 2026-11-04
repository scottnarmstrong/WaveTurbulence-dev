/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SourceCoupleJointIntegrability
public import WaveTurbulence.Foundations.Incoh.CoupleSpectralMixtureDecay

/-!
# Decay of the actual source couple spectral extension

TARGET (incohproof8–20). All spectral measurability and Fubini premises
are discharged from source spatial norms and proved root-marginal bounds.
The remaining coefficient is the literal, previously bounded spectral mass.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Actual localized source decay, with no assumed Fourier or joint-integrability bound. -/
theorem exists_sourceCoupleExtension_bound (d : ℕ) (hd : 3 ≤ d)
    (η : ℝ) (hη : 0 < η) (hη₁ : η ≤ 1 / 3) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n m w K M : ℕ,
        ∀ P : MomentumTreeData n m w, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        1 ≤ incoherenceCount Q → ∀ R : RootCoordinates n,
        ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I →
        I ⊆ univ.pi (fun i => linkBox (Q i)) →
        ∀ f : Fin m → Mom d → ℂ, ∀ B : ℝ, d + 1 ≤ K → 0 ≤ B →
        (∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) →
        ∀ c : Fin m → Fin d → ℤ, ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ ζ : Circle,
        Fourier.mixedFourierNorm00 η (P.sourceCoupleExtension ζ R L γ δ Q I f c z) ≤
          (∫⁻ ξ : LocalizedCellIndex n m → Fin d → ℝ,
            ‖localizedSpectralReference (n := n) f c ξ‖ₑ) *
          ENNReal.ofReal ((C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_coupleSpectralMixture_bound d hd η hη hη₁
  obtain ⟨Cᵣ, _, hr⟩ := exists_rootDensity_L1_bound d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₁, hL₁, hb⟩ := hb γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₂, _, hr⟩ := hr γ hγ η hη hηγ δ hδ D hD
  refine ⟨max L₁ L₂, hL₁.trans (le_max_left _ _), ?_⟩
  intro L hL n m w K M P Q hspan hg R I hI hbox f B hK hB hf c z ζ
  have hLa := (le_max_left L₁ L₂).trans hL
  have hLr := (le_max_right L₁ L₂).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le (hL₁.trans hLa)
  let E := fun ξ : LocalizedCellIndex n m → Fin d → ℝ =>
    ‖P.sourceSpectralAmplitude ζ f c z 0 ξ‖ₑ
  have hE : Measurable E := (P.continuous_sourceSpectralAmplitude ζ f c z hK hB hf 0).measurable.enorm
  have hA (k : Mom d) (ξ : LocalizedCellIndex n m → Fin d → ℝ) :
      ‖P.sourceSpectralAmplitude ζ f c z k ξ‖ₑ ≤ E ξ := by
    dsimp only [E]
    rw [P.enorm_sourceSpectralAmplitude, P.enorm_sourceSpectralAmplitude]
  have hj (k : Mom d) := P.integrable_sourceCoupleMixture_of_uniformRootL1 ζ R L γ δ Q I hI hbox
    f c z hLp hK hB hf
    (N := ENNReal.ofReal ((Cᵣ * δ) ^ n *
      L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q))) ENNReal.ofReal_lt_top
    (fun ξ => by
      simpa only [P.incoherenceCount_spectralLinks] using
        hr L hLr n (P.spectralLinks Q z ξ) hspan I hI hbox R) k
  have hbound := hb L hLa n (incoherenceCount Q) hg
    (LocalizedCellIndex n m → Fin d → ℝ) (Mom d) inferInstance volume inferInstance
    (P.spectralLinks Q z) (fun _ => rfl) (fun _ => hspan) (fun _ => I) (fun _ => hI)
    (fun _ => hbox) R (P.sourceSpectralAmplitude ζ f c z) E hE hA
    (P.stronglyMeasurable_spectral_coupleExtension R hLp γ δ Q z hI contDiff_rootCutoff.continuous.measurable) hj
  have he : E = fun ξ => ‖localizedSpectralReference (n := n) f c ξ‖ₑ := by
    funext ξ
    exact P.enorm_sourceSpectralAmplitude ζ f c z 0 ξ
  change Fourier.mixedFourierNorm00 η (fun t k =>
    ∫ ξ : LocalizedCellIndex n m → Fin d → ℝ, P.sourceSpectralAmplitude ζ f c z k ξ *
      R.coupleExtension rootCutoff L γ δ (P.spectralLinks Q z ξ) I t) ≤ _
  simpa only [he] using hbound

end WaveTurbulence.Incoh
