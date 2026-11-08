/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltSrc.SpectralMeas
public import WaveTurbulence.Foundations.Flower.IncTop.Top.RootMixture
public import WaveTurbulence.Foundations.Flower.IncTop.Top.RootJets
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.WeightedCoupleExtension

/-! # D5b-3 FILT-GATE: the filtered couple extensions and their root-mixture bound at any weight `θ`

Twins (copied by source from INC-TOP, sha256 in COPIED-SHA256SUMS; `φ` inserted after the links):
- `Reg/AllCellMaskedCoupleDecay.allCellMaskedSourceCoupleExtensionSpatial` → `…SpatialFilt`;
- `Reg/WeightedCoupleExtension.fourierMaskedSourceCoupleExtension` → `…Filt`;
- the body of `Top/CoupleRootExtension.exists_rootMaskedCoupleExtension_bound`, with the time weight `θ` free and the
  per-cell physical and Fourier bounds as hypotheses (`rootMaskedCoupleExtensionFilt_le_of_cells`): this is where the
  two weights of the gate (`θ = η` and `θ = 1/4`) enter, through the cell bound only (o82 §15: "no new cutoff
  derivative or time oscillation"). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.FiltGate
open WaveTurbulence.Incoh WaveTurbulence.Flower.IncTop WaveTurbulence.Flower.FiltSrc

/-- Filtered all-cell source extension with its fixed smooth root masks. -/
def MomentumTreeData.allCellMaskedSourceCoupleExtensionSpatialFilt {d n m w : ℕ}
    (P : MomentumTreeData n m w) (χ : ℝ → ℝ) (ζ : Circle) (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (I : Set (Fin n → Fin 2 → ℝ))
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (τ t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  ∫ u, (MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S k u *
    (MomentumTreeData.allCellCutoffCoupleKernelSpatialFilt (P := P)) χ R L γ δ Q φ I S (t + τ) u ∂sourceCellMeasure S

/-- One common filtered spectral extension, with the Fourier parameter inside the spectral integral. -/
def MomentumTreeData.fourierMaskedSourceCoupleExtensionFilt {d n m w : ℕ} {α : Type}
    [MeasurableSpace α] (P : MomentumTreeData n m w) (F : Cut2A.SpatialMeasure (PairedMomentum d n) α)
    (χ : ℝ → ℝ) (ζ : Circle) (R : RootCoordinates n) (L γ δ : ℝ)
    (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (I : Set (Fin n → Fin 2 → ℝ)) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (τ t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  ∫ u, F.amplitude u.2 * (MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S k u.1 *
    (MomentumTreeData.allCellCutoffCoupleKernelSpatialFilt (P := P)) χ R L γ δ (spatialFrequencyLinks Q (F.frequency u.2))
      φ I S (t + τ) u.1 ∂(sourceCellMeasure S).prod F.μ

/-- **The root-modulated filtered couple extension bound at any time weight `θ`**, from per-cell bounds: every
spectral cell extension is integrable, has physical `L¹` norm `≤ H < ⊤` and `X^θ` norm `≤ Z`. The cost is INC-TOP's
(`exists_rootMaskedCoupleExtension_bound`): `rootJetConstant J · (cell constant · G.momentMass J) · Z`. -/
theorem rootMaskedCoupleExtensionFilt_le_of_cells {d n m w J W K M : ℕ}
    (P : MomentumTreeData n m w) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (R : RootCoordinates n)
    {L : ℝ} (hLp : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (I : Set (Fin n → Fin 2 → ℝ)) (hI : MeasurableSet I) (f : Fin m → Mom d → ℂ) {B : ℝ}
    (hK : d + 1 + J ≤ K) (hM : W + 2 * d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ)) {C : ℝ}
    (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) (τ : Fin 2 → ℝ) (ζ : Circle)
    {α : Type} [MeasurableSpace α] (G : RootMeasure d n α) (hfin : G.momentMass J < ⊤) (θ : ℝ)
    {H Z : ℝ≥0∞} (hH : H < ⊤)
    (hint : ∀ (z : (Fin n × Fin 2) → Fin d → ℤ) (ξ : LocalizedCellIndex n m → Fin d → ℝ) (a : α),
      Integrable (RootCoordinates.coupleExtensionFilt R χ L γ δ
        ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (G.base.frequency a)) z ξ) φ I))
    (hphys : ∀ (z : (Fin n × Fin 2) → Fin d → ℤ) (ξ : LocalizedCellIndex n m → Fin d → ℝ) (a : α),
      eLpNorm (RootCoordinates.coupleExtensionFilt R χ L γ δ
        ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (G.base.frequency a)) z ξ) φ I) 1 ≤ H)
    (hdecay : ∀ (z : (Fin n × Fin 2) → Fin d → ℤ) (ξ : LocalizedCellIndex n m → Fin d → ℝ) (a : α),
      Fourier.timeFourierNorm θ (RootCoordinates.coupleExtensionFilt R χ L γ δ
        ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (G.base.frequency a)) z ξ) φ I) ≤ Z) :
    Fourier.mixedFourierNorm θ J W
      (fun t k => (MomentumTreeData.fourierMaskedSourceCoupleExtensionFilt (P := P)) (G.at k) χ ζ R L γ δ Q φ I f S τ t k) ≤
      ENNReal.ofReal (rootJetConstant J) *
        ((ENNReal.ofReal (maskedSourceSpatialConstantSpatial d m J W) * ENNReal.ofReal (C ^ n) *
          (ENNReal.ofReal (leafWeightedMomentLocalizationConstant d J M W * B) ^ m *
            ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n))) * G.momentMass J) * Z := by
  let Kt := fun t (u : (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) × α) =>
    (MomentumTreeData.allCellCutoffCoupleKernelSpatialFilt (P := P)) χ R L γ δ
      (spatialFrequencyLinks Q (G.base.frequency u.2)) φ I S (t + τ) u.1
  have hGbase := (MomentumTreeData.stronglyMeasurable_coupleSpatialFrequencyFilt (P := P)) G.base.frequency
    G.base.frequency_measurable hχ.continuous.measurable R hLp γ δ Q φ I hI S
  have hK' : StronglyMeasurable (fun v : (Fin 2 → ℝ) ×
      ((SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) × α) => Kt v.1 v.2) :=
    hGbase.comp_measurable (g := fun v : (Fin 2 → ℝ) ×
      ((SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) × α) => (v.1 + τ, v.2))
      ((measurable_fst.add_const τ).prodMk measurable_snd)
  have hiK (u : (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) × α) :
      Integrable (fun t => Kt t u) :=
    (hint u.1.1.2.val u.1.2 u.2).comp_add_right τ
  have hphys' (u : (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) × α) :
      eLpNorm (fun t => Kt t u) 1 ≤ H := by
    have heq : eLpNorm (fun t => Kt t u) 1 =
        eLpNorm (RootCoordinates.coupleExtensionFilt R χ L γ δ
          ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (G.base.frequency u.2))
            u.1.1.2.val u.1.2) φ I) 1 :=
      eLpNorm_comp_measurePreserving (hint u.1.1.2.val u.1.2 u.2).aestronglyMeasurable
        (measurePreserving_add_right volume τ)
    rw [heq]
    exact hphys u.1.1.2.val u.1.2 u.2
  have hdecay' (u : (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) × α) :
      Fourier.timeFourierNorm θ (fun t => Kt t u) ≤ Z := by
    change Fourier.timeFourierNorm θ
      (fun t => RootCoordinates.coupleExtensionFilt R χ L γ δ
        ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (G.base.frequency u.2))
          u.1.1.2.val u.1.2) φ I (t + τ)) ≤ _
    rw [Fourier.timeFourierNorm_translate]
    exact hdecay u.1.1.2.val u.1.2 u.2
  have hE := integrable_maskedCellEnvelopeSpatial J W f S hS hK hM hB hf
  have hfull := mixedFourierNorm_rootProductMixture_le (N := J) (M := W) (sourceCellMeasure S) G θ
    ((MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S) (maskedCellEnvelopeSpatial J W f S) Kt
    (fun u => ((MomentumTreeData.contDiff_allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S u).of_le (by simp))
    (fun j _ k => stronglyMeasurable_rootMaskedJets P ζ f S G.root_measurable (by omega) hB hf k j)
    hE (measurable_maskedCellEnvelopeSpatial J W f S (by omega) hB hf)
    (maskedCellEnvelope_nonnegSpatial J W f S)
    (fun j hj k u => MomentumTreeData.weighted_norm_allCellMaskedAmplitudeDerivative_leSpatial (P := P) ζ f S hj k u)
    hK' hiK hH hphys' hdecay' hfin
  change Fourier.mixedFourierNorm θ J W
    (fun t k => ∫ u, (G.at k).amplitude u.2 *
      (MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S k u.1 *
      Kt t u ∂(sourceCellMeasure S).prod G.base.μ) ≤ _
  apply hfull.trans
  gcongr
  exact lintegral_maskedCellEnvelope_leSpatial J W f S hS hK hM hB hf

end WaveTurbulence.Flower.FiltGate
