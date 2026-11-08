/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Top.RootMixture
public import WaveTurbulence.Foundations.Flower.IncTop.Top.RootJets
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.WeightedCoupleExtension

/-! Ported by source from C2-B-TOP `C2BTop.CoupleRootExtension` (sha256 in COPIED-SHA256SUMS); mechanical edits only.
 # Root-modulated couple spectral extension: full root derivative bound

C2-B-REG's `exists_fourierMaskedSourceCoupleExtension_bound` for the `k`-dependent Fourier measure
`G.at k`.  The extension is C2-B-REG's literal `fourierMaskedSourceCoupleExtension` evaluated with the
measure `G.at k` at the root momentum `k`.  The cost of the root character is
`rootJetConstant J * G.momentMass J` in place of `F.mass`; every other constant and the decay rate are
C2-B-REG's. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff
namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh

/-- The root-modulated couple extension bound.  Constants and thresholds precede the measure. -/
theorem exists_rootMaskedCoupleExtension_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 3 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      η < incoherenceExponent d γ →
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
        ∀ {α : Type} [MeasurableSpace α] (G : RootMeasure d n α), G.momentMass J < ⊤ →
        Fourier.mixedFourierNorm η J W
          (fun t k => (MomentumTreeData.fourierMaskedSourceCoupleExtension (P := P)) (G.at k) χ ζ R L γ δ Q I f S τ t k) ≤
          ENNReal.ofReal (rootJetConstant J) *
            ((ENNReal.ofReal (maskedSourceSpatialConstantSpatial d m J W) * ENNReal.ofReal (C ^ n) *
              (ENNReal.ofReal (leafWeightedMomentLocalizationConstant d J M W * B) ^ m *
                ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n))) * G.momentMass J) *
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
  intro L hL n m w J W K M P Q hspan hg R I hI hbox f B hK hM hB hf S C hS τ ζ α _ G hfin
  have hLa := (le_max_left L₁ L₂).trans hL
  have hLr := (le_max_right L₁ L₂).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le (hL₁.trans hLa)
  let Kt := fun t (u : (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) × α) =>
    (MomentumTreeData.allCellCutoffCoupleKernelSpatial (P := P)) χ R L γ δ (spatialFrequencyLinks Q (G.base.frequency u.2)) I S
      (t + τ) u.1
  let Nr := ENNReal.ofReal ((Cᵣ * δ) ^ n *
    L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q))
  have hroot (z : (Fin n × Fin 2) → Fin d → ℤ) (ξ : LocalizedCellIndex n m → Fin d → ℝ) (a : α) :
      eLpNorm (R.linkDensity L γ δ
        ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (G.base.frequency a)) z ξ) I) 1 ≤ Nr := by
    simpa only [(MomentumTreeData.incoherenceCount_spectralLinksSpatial (P := P)), incoherenceCount_spatialFrequencyLinks] using
      hr L hLr n ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (G.base.frequency a)) z ξ) hspan I hI hbox R
  have hGbase := (MomentumTreeData.stronglyMeasurable_coupleSpatialFrequency (P := P)) G.base.frequency
    G.base.frequency_measurable hχ.continuous.measurable R hLp γ δ Q I hI S
  have hK' : StronglyMeasurable (fun v : (Fin 2 → ℝ) ×
      ((SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) × α) => Kt v.1 v.2) :=
    hGbase.comp_measurable (g := fun v : (Fin 2 → ℝ) ×
      ((SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) × α) => (v.1 + τ, v.2))
      ((measurable_fst.add_const τ).prodMk measurable_snd)
  have hiK (u : (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) × α) :
      Integrable (fun t => Kt t u) :=
    (R.integrable_coupleExtension hχ hctrl hLp γ δ
      ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (G.base.frequency u.2)) u.1.1.2.val u.1.2)
        hI hbox).comp_add_right τ
  have hphys (u : (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) × α) :
      eLpNorm (fun t => Kt t u) 1 ≤ Cphys * Nr := by
    have hi := R.integrable_coupleExtension hχ hctrl hLp γ δ
      ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (G.base.frequency u.2)) u.1.1.2.val u.1.2) hI hbox
    have heq : eLpNorm (fun t => Kt t u) 1 =
        eLpNorm (R.coupleExtension χ L γ δ
          ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (G.base.frequency u.2)) u.1.1.2.val u.1.2) I) 1 :=
      eLpNorm_comp_measurePreserving hi.aestronglyMeasurable (measurePreserving_add_right volume τ)
    rw [heq]
    exact (R.eLpNorm_coupleExtension_one_le hχ hctrl hLp γ δ
      ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (G.base.frequency u.2)) u.1.1.2.val u.1.2)
        hI hbox).trans (mul_le_mul' le_rfl (hroot u.1.1.2.val u.1.2 u.2))
  have hdecay (u : (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) × α) :
      Fourier.timeFourierNorm η (fun t => Kt t u) ≤ ENNReal.ofReal ((C₀ * δ) ^ n *
        L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q)) := by
    change Fourier.timeFourierNorm η
      (fun t => R.coupleExtension χ L γ δ
        ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (G.base.frequency u.2)) u.1.1.2.val u.1.2) I
          (t + τ)) ≤ _
    rw [Fourier.timeFourierNorm_translate]
    simpa only [(MomentumTreeData.incoherenceCount_spectralLinksSpatial (P := P)), incoherenceCount_spatialFrequencyLinks] using
      hb L hLa n ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (G.base.frequency u.2)) u.1.1.2.val u.1.2)
        hg hspan I hI hbox R
  have hE := integrable_maskedCellEnvelopeSpatial J W f S hS hK hM hB hf
  have hfull := mixedFourierNorm_rootProductMixture_le (N := J) (M := W) (sourceCellMeasure S) G η
    ((MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S) (maskedCellEnvelopeSpatial J W f S) Kt
    (fun u => ((MomentumTreeData.contDiff_allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S u).of_le (by simp))
    (fun j _ k => stronglyMeasurable_rootMaskedJets P ζ f S G.root_measurable (by omega) hB hf k j)
    hE (measurable_maskedCellEnvelopeSpatial J W f S (by omega) hB hf)
    (maskedCellEnvelope_nonnegSpatial J W f S)
    (fun j hj k u => MomentumTreeData.weighted_norm_allCellMaskedAmplitudeDerivative_leSpatial (P := P) ζ f S hj k u)
    hK' hiK (ENNReal.mul_lt_top hCphys ENNReal.ofReal_lt_top) hphys hdecay hfin
  change Fourier.mixedFourierNorm η J W
    (fun t k => ∫ u, (G.at k).amplitude u.2 * (MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S k u.1 *
      Kt t u ∂(sourceCellMeasure S).prod G.base.μ) ≤ _
  apply hfull.trans
  gcongr
  exact lintegral_maskedCellEnvelope_leSpatial J W f S hS hK hM hB hf

end WaveTurbulence.Flower.IncTop