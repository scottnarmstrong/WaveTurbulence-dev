/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.AllCellMaskedCoupleDecay
public import WaveTurbulence.Foundations.Incoh.CoupleCutoffUniformDecay
public import WaveTurbulence.Foundations.Incoh.AllCellCutoffCoupleFamily
public import WaveTurbulence.Foundations.Incoh.CoupleExtensionAgreement
public import WaveTurbulence.Foundations.Incoh.CouplePhysicalL1
public import WaveTurbulence.Foundations.Incoh.UniformL1MixtureIntegrability
public import WaveTurbulence.Foundations.Incoh.SpectralSpatialMixture

/-! # Full spatial source decay with cutoff-independent exponential constant

TARGET Proposition 5.1, couple case. Every spatial derivative and root
weight is taken on the actual masked source extension. Input Fourier
moments, summability, differentiation and Fubini are proved internally.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Incoh

/-- Actual full weighted spatial mixed-norm decay with all analytic conditions discharged from
source input norms. Constants and lattice threshold precede every order and source object. -/
theorem exists_allCellMaskedSourceCoupleExtension_cutoffUniform_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 3 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n m w J W K M : ℕ,
        ∀ P : MomentumTreeData n m w, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        1 ≤ incoherenceCount Q → ∀ R : RootCoordinates n,
        ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
        ∀ f : Fin m → Mom d → ℂ, ∀ B : ℝ, d + 1 + J ≤ K → W + 2 * d ≤ M → 0 ≤ B →
        (∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) →
        ∀ S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ),
        ∀ C : ℝ, (∀ c, ((S c).card : ℝ) ≤ C ^ n) → ∀ τ : Fin 2 → ℝ, ∀ ζ : Circle,
        Fourier.mixedFourierNorm η J W (P.allCellMaskedSourceCoupleExtension χ ζ R L γ δ Q I f S τ) ≤
          (ENNReal.ofReal (maskedSourceSpatialConstant d m J W) * ENNReal.ofReal (C ^ n) *
            (ENNReal.ofReal (leafWeightedMomentLocalizationConstant d J M W * B) ^ m *
              ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n))) *
            ENNReal.ofReal ((C₀ * δ) ^ n *
              L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_coupleExtension_cutoffUniform_decay d hd
  obtain ⟨Cᵣ, _, hr⟩ := exists_rootDensity_L1_bound d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro η hη hη₁ χ hχ hc
  obtain ⟨hctrl⟩ := Fourier.exists_cutoffControl hχ hc
  let Cphys := Fourier.cutoffKernelL1Factor hctrl.radius hctrl.bound *
    Fourier.localTimeL1Factor 1 hctrl.radius hctrl.bound
  have hCphys : Cphys < ⊤ := ENNReal.mul_lt_top (Fourier.cutoffKernelL1Factor_ne_top _ _).lt_top
    (Fourier.localTimeL1Factor_ne_top (le_refl (1 : ℝ)) _ _).lt_top
  intro γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₁, hL₁, hb⟩ := hb η hη hη₁ χ hχ hc γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₂, _, hr⟩ := hr γ hγ η hη hηγ δ hδ D hD
  refine ⟨max L₁ L₂, hL₁.trans (le_max_left _ _), ?_⟩
  intro L hL n m w J W K M P Q hspan hg R I hI hbox f B hK hM hB hf S C hS τ ζ
  have hLa := (le_max_left L₁ L₂).trans hL
  have hLr := (le_max_right L₁ L₂).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le (hL₁.trans hLa)
  let A := P.allCellMaskedSpectralAmplitude ζ f S
  let E := maskedCellEnvelope J W f S
  let G := fun t u => P.allCellCutoffCoupleKernel χ R L γ δ Q I S (t + τ) u
  let Nr := ENNReal.ofReal ((Cᵣ * δ) ^ n *
    L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q))
  have hroot (z : (Fin n × Fin 2) → Fin d → ℤ) (ξ : LocalizedCellIndex n m → Fin d → ℝ) :
      eLpNorm (R.linkDensity L γ δ (P.spectralLinks Q z ξ) I) 1 ≤ Nr := by
    simpa only [P.incoherenceCount_spectralLinks] using
      hr L hLr n (P.spectralLinks Q z ξ) hspan I hI hbox R
  have hE := integrable_maskedCellEnvelope J W f S hS hK hM hB hf
  have hA0 (k : Mom d) : StronglyMeasurable (A k) :=
    P.stronglyMeasurable_allCellMaskedSpectralAmplitude ζ f S (by omega) hB hf k
  have hnorm (k : Mom d) (u : SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) : ‖A k u‖ ≤ E u := by
    have hh := P.weighted_norm_allCellMaskedAmplitudeDerivative_le ζ f S (J := J) (W := W) (by omega : 0 ≤ J) k u
    simp only [norm_iteratedFDeriv_zero] at hh
    exact (le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (one_le_momentumBracket k))).trans hh
  have hGbase := P.stronglyMeasurable_allCellCutoffCoupleKernel hχ.continuous.measurable R hLp γ δ Q I hI S
  have hG : StronglyMeasurable (fun v : (Fin 2 → ℝ) ×
      (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) => G v.1 v.2) :=
    hGbase.comp_measurable
      (g := fun v : (Fin 2 → ℝ) × (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) =>
        (v.1 + τ, v.2)) (by fun_prop)
  have hiG (u : SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) : Integrable (fun t => G t u) :=
    (R.integrable_coupleExtension hχ hctrl hLp γ δ (P.spectralLinks Q u.1.2.val u.2) hI hbox).comp_add_right τ
  have hphys (u : SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) :
      eLpNorm (fun t => G t u) 1 ≤ Cphys * Nr := by
    have hi := R.integrable_coupleExtension hχ hctrl hLp γ δ (P.spectralLinks Q u.1.2.val u.2) hI hbox
    have heq : eLpNorm (fun t => G t u) 1 =
        eLpNorm (R.coupleExtension χ L γ δ (P.spectralLinks Q u.1.2.val u.2) I) 1 :=
      eLpNorm_comp_measurePreserving hi.aestronglyMeasurable (measurePreserving_add_right volume τ)
    rw [heq]
    exact (R.eLpNorm_coupleExtension_one_le hχ hctrl hLp γ δ (P.spectralLinks Q u.1.2.val u.2) hI hbox).trans
      (mul_le_mul' le_rfl (hroot _ _))
  have hjoint (k : Mom d) := integrable_amplitude_mul_family_of_uniformL1 (sourceCellMeasure S)
    (A k) (hA0 k) (hE.mono' (hA0 k).aestronglyMeasurable (ae_of_all _ (hnorm k))) G hG hiG
    (ENNReal.mul_lt_top hCphys ENNReal.ofReal_lt_top) hphys
  have hfull := mixedFourierNorm_spectralMixture_le (N := J) (M := W) (sourceCellMeasure S) η A E G
    (fun u => (P.contDiff_allCellMaskedSpectralAmplitude ζ f S u).of_le (by simp))
    (fun j _ k => (P.stronglyMeasurable_allCellMaskedAmplitudeDerivative ζ f S (by omega) hB hf k j).aestronglyMeasurable)
    hE (measurable_maskedCellEnvelope J W f S (by omega) hB hf) (maskedCellEnvelope_nonneg J W f S)
    (fun j hj k u => P.weighted_norm_allCellMaskedAmplitudeDerivative_le ζ f S hj k u)
    hG hiG hjoint (ENNReal.mul_lt_top hCphys ENNReal.ofReal_lt_top) hphys
  apply hfull.trans
  calc
    _ ≤ ∫⁻ u, ENNReal.ofReal (E u) * ENNReal.ofReal ((C₀ * δ) ^ n *
        L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q)) ∂sourceCellMeasure S := by
      apply lintegral_mono
      intro u
      apply mul_le_mul' le_rfl
      change Fourier.timeFourierNorm η
        (fun t => R.coupleExtension χ L γ δ (P.spectralLinks Q u.1.2.val u.2) I (t + τ)) ≤ _
      rw [Fourier.timeFourierNorm_translate]
      simpa only [P.incoherenceCount_spectralLinks] using
        hb L hLa n (P.spectralLinks Q u.1.2.val u.2) hg hspan I hI hbox R
    _ = _ := lintegral_mul_const _ (ENNReal.measurable_ofReal.comp
      (measurable_maskedCellEnvelope J W f S (by omega) hB hf))
    _ ≤ _ := mul_le_mul' (lintegral_maskedCellEnvelope_le J W f S hS hK hM hB hf) le_rfl

end WaveTurbulence.Incoh
