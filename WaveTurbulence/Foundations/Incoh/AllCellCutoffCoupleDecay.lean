/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.AllCellCutoffCoupleFubini
public import WaveTurbulence.Foundations.Incoh.CutoffCoupleSpectralMixtureDecay

/-!
# Decay after actual countable couple localization recombination

TARGET (incohproof8–20). The common spectral envelope is integrated only
after the momentum supremum. All actual cell and spectral variables are
recombined against their literal counting/Lebesgue measure.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Incoh

/-- The actual countable-cell spectral couple extension. -/
@[expose] def MomentumTreeData.allCellSourceCutoffCoupleExtension {d n m w : ℕ}
    (P : MomentumTreeData n m w) (χ : ℝ → ℝ) (ζ : Circle) (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  ∫ u, P.allCellSpectralAmplitude ζ f S k u * P.allCellCutoffCoupleKernel χ R L γ δ Q I S t u
    ∂sourceCellMeasure S

/-- Actual recombined couple decay, with all input Fourier and Fubini bounds proved. -/
theorem exists_allCellSourceCutoffCoupleExtension_bound (d : ℕ) (hd : 3 ≤ d)
    (η : ℝ) (hη : 0 < η) (hη₁ : η ≤ 1 / 3)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n m w K M : ℕ,
        ∀ P : MomentumTreeData n m w, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        1 ≤ incoherenceCount Q → ∀ R : RootCoordinates n,
        ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I →
        I ⊆ univ.pi (fun i => linkBox (Q i)) →
        ∀ f : Fin m → Mom d → ℂ, ∀ B : ℝ, d + 1 ≤ K → 2 * d ≤ M → 0 ≤ B →
        (∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) →
        ∀ S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ),
        ∀ C : ℝ, (∀ c, ((S c).card : ℝ) ≤ C ^ n) → ∀ ζ : Circle,
        Fourier.mixedFourierNorm00 η (P.allCellSourceCutoffCoupleExtension χ ζ R L γ δ Q I f S) ≤
          (ENNReal.ofReal (C ^ n) * (ENNReal.ofReal (leafLocalizationConstant d M * B) ^ m *
            ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n))) *
          ENNReal.ofReal ((C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_cutoffCoupleSpectralMixture_bound d hd η hη hη₁ hχ hc
  obtain ⟨Cᵣ, _, hr⟩ := exists_rootDensity_L1_bound d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₁, hL₁, hb⟩ := hb γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₂, _, hr⟩ := hr γ hγ η hη hηγ δ hδ D hD
  refine ⟨max L₁ L₂, hL₁.trans (le_max_left _ _), ?_⟩
  intro L hL n m w K M P Q hspan hg R I hI hbox f B hK hM hB hf S C hS ζ
  have hLa := (le_max_left L₁ L₂).trans hL
  have hLr := (le_max_right L₁ L₂).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le (hL₁.trans hLa)
  let U := SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)
  let E := fun u : U => ‖localizedSpectralReference (n := n) f u.1.1 u.2‖ₑ
  have hA (k : Mom d) (u : U) : ‖P.allCellSpectralAmplitude ζ f S k u‖ₑ ≤ E u :=
    (P.enorm_sourceSpectralAmplitude ζ f u.1.1 u.1.2.val k u.2).le
  obtain ⟨hctrl⟩ := Fourier.exists_cutoffControl hχ hc
  have hj (k : Mom d) := P.integrable_allCellCutoffCoupleMixture_of_uniformRootL1 hχ hctrl ζ R L γ δ Q I hI hbox
    f S hS hLp hK hM hB hf
    (N := ENNReal.ofReal ((Cᵣ * δ) ^ n *
      L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q))) ENNReal.ofReal_lt_top
    (fun z ξ => by
      simpa only [P.incoherenceCount_spectralLinks] using
        hr L hLr n (P.spectralLinks Q z ξ) hspan I hI hbox R) k
  have hbound := hb L hLa n (incoherenceCount Q) hg U (Mom d) inferInstance
    (sourceCellMeasure S) inferInstance
    (fun u : U => P.spectralLinks Q u.1.2.val u.2) (fun _ => rfl) (fun _ => hspan)
    (fun _ => I) (fun _ => hI) (fun _ => hbox) R (P.allCellSpectralAmplitude ζ f S) E
    (measurable_allCellSpectralReference S f hK hB hf) hA
    (P.stronglyMeasurable_allCellCutoffCoupleKernel hχ.continuous.measurable R hLp γ δ Q I hI S) hj
  change Fourier.mixedFourierNorm00 η (fun t k => ∫ u,
    P.allCellSpectralAmplitude ζ f S k u * P.allCellCutoffCoupleKernel χ R L γ δ Q I S t u
      ∂sourceCellMeasure S) ≤ _
  exact hbound.trans (mul_le_mul' (lintegral_sourceCellMeasure_reference_le S hS f hK hM hB hf) le_rfl)

end WaveTurbulence.Incoh
