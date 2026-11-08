/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.ProductRootMixture
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.TreeRootSpatialDecay

/-! Ported by source from C2-B-TOP `Cut2BReg.WeightedTreeExtension` (sha256 in COPIED-SHA256SUMS); mechanical edits only.
 # Full tree derivatives for actual Fourier-measure spectral extensions -/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- The common tree extension on the product source/character measure. -/
@[expose] def MomentumTreeData.fourierRootPartitionSourceTreeExtension {d n m w : ℕ} {α : Type}
    [MeasurableSpace α] (P : MomentumTreeData n m w) (F : Cut2A.SpatialMeasure (PairedMomentum d n) α)
    (ζ : Circle) (R : RootCoordinates n) (χ : ℝ → ℝ) (L γ δ : ℝ)
    (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ)) (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  ∫ u, F.amplitude u.2 * rootAmplitudeSumSpatial ((MomentumTreeData.treeRootSpectralAmplitudeSpatial (P := P)) ζ f S) k u.1 *
    (MomentumTreeData.allCellTreeKernelSpatial (P := P.withRootInput)) R χ L γ δ (spatialFrequencyLinks Q (F.frequency u.2)) I S
      t u.1 ∂(sourceCellMeasure S).prod F.μ

/-- TARGET 5.1's full tree root derivatives, at exactly the Fourier mass cost.
The common time Fourier supremum includes all character parameters. -/
theorem exists_fourierRootPartitionSourceTreeExtension_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ l : ℕ, l ≤ 2 → ∀ η : ℝ, 0 < η → η ≤ 1 / 100 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n m w J K M : ℕ,
        ∀ P : MomentumTreeData n m w, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        1 ≤ incoherenceCount Q → ∀ R : RootCoordinates n, ∀ T : TreeClockFibers l Q,
        R.rootVertex 0 = T.selection.coordinates.rootVertex 0 →
        R.rootVertex 1 = T.selection.coordinates.rootVertex (Fin.last (l + 1)) →
        (∀ v ∈ R.rootBox Q, ∀ j, χ (v j) = 1) →
        (∀ v ∈ T.selection.coordinates.rootBox Q, ∀ j, χ (v j) = 1) →
        ∀ f : Fin m → Mom d → ℂ, ∀ B : ℝ, d + 1 + J ≤ K → 2 * d ≤ M → 0 ≤ B →
        (∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) →
        ∀ S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ),
        ∀ C : ℝ, (∀ c, ((S c).card : ℝ) ≤ C ^ n) → ∀ ζ : Circle,
        ∀ {α : Type} [MeasurableSpace α] (F : Cut2A.SpatialMeasure (PairedMomentum d n) α),
        Measurable F.amplitude →
        Fourier.mixedFourierNorm η J 0
          ((MomentumTreeData.fourierRootPartitionSourceTreeExtension (P := P)) F ζ R χ L γ δ Q T.timeDomain f S) ≤
          ENNReal.ofReal F.mass * ((ENNReal.ofReal (rootLocalOverlapConstantSpatial d) *
            (ENNReal.ofReal (treeRootAmplitudeDerivativeFactorSpatial d J) *
              ENNReal.ofReal (maskedSourceSpatialConstantSpatial d (m + 1) J 0) * ENNReal.ofReal (C ^ n) *
                (ENNReal.ofReal (leafMomentLocalizationConstant d J M * treeAugmentedInputBoundSpatial d K M B) ^ (m + 1) *
                  ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n)))) *
            ENNReal.ofReal ((C₀ * δ) ^ n *
              L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q))) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_parameterTreeCausalExtension_decay d hd
  obtain ⟨Cᵣ, _, hr⟩ := exists_rootDensity_L1_bound d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro l hl η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨hc⟩ := Fourier.exists_cutoffControl hχ hcχ
  obtain ⟨L₁, hL₁, hb⟩ := hb l hl η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₂, _, hr⟩ := hr γ hγ η hη hηγ δ hδ D hD
  refine ⟨max L₁ L₂, hL₁.trans (le_max_left _ _), ?_⟩
  intro L hL n m w J K M P Q hspan hg R T hfirst hlast hχroot hχsel f B hK hM hB hf S C hS ζ α _ F hamp
  have hLa := (le_max_left L₁ L₂).trans hL
  have hLr := (le_max_right L₁ L₂).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le (hL₁.trans hLa)
  let U := SourceCellIndex S × (LocalizedCellIndex n (m + 1) → Fin d → ℝ)
  let G := fun t (u : U × α) => (MomentumTreeData.allCellTreeKernelSpatial (P := P.withRootInput)) R χ L γ δ
    (spatialFrequencyLinks Q (F.frequency u.2)) T.timeDomain S t u.1
  let Nr := ENNReal.ofReal ((Cᵣ * δ) ^ n *
    L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q))
  let Cphys := Fourier.cutoffKernelL1Factor hc.radius hc.bound * Fourier.localTimeL1Factor 1 hc.radius hc.bound
  have hCphys : Cphys < ⊤ := ENNReal.mul_lt_top (Fourier.cutoffKernelL1Factor_ne_top _ _).lt_top
    (Fourier.localTimeL1Factor_ne_top (le_refl (1 : ℝ)) _ _).lt_top
  have hphys (u : U × α) :
      eLpNorm (fun t => G t u) 1 ≤ Cphys * Nr := by
    apply (eLpNorm_cutoffTriangleIntegral_one_le hχ hc
      (R.integrable_linkDensity hLp γ δ ((MomentumTreeData.spectralLinksSpatial (P := P.withRootInput)) (spatialFrequencyLinks Q (F.frequency u.2)) u.1.1.2.val u.1.2)
        T.measurableSet_timeDomain T.timeDomain_subset_linkBoxes)).trans
    apply mul_le_mul' le_rfl
    exact hr L hLr n ((MomentumTreeData.spectralLinksSpatial (P := P.withRootInput)) (spatialFrequencyLinks Q (F.frequency u.2)) u.1.1.2.val u.1.2) hspan
      T.timeDomain T.measurableSet_timeDomain T.timeDomain_subset_linkBoxes R
  have hfull := mixedFourierNorm_productRootMixture_le (N := J) (sourceCellMeasure S) F hamp η
    ((MomentumTreeData.treeRootSpectralAmplitudeSpatial (P := P)) ζ f S) (treeRootSpectralEnvelopeSpatial J f S)
    ((MomentumTreeData.treeRootSpectralAmplitude_eq_zeroSpatial (P := P)) ζ f S)
    (fun q u => ((MomentumTreeData.contDiff_treeRootSpectralAmplitudeSpatial (P := P)) ζ f S q u).of_le (by simp))
    (fun q j _ k => (MomentumTreeData.stronglyMeasurable_treeRootAmplitudeDerivativeSpatial (P := P)) ζ f S (by omega) hf q k j)
    (integrable_treeRootSpectralEnvelopeSpatial J f S hS hK hM hf)
    (measurable_treeRootSpectralEnvelopeSpatial J f S (by omega) hf)
    (treeRootSpectralEnvelope_nonnegSpatial J f S)
    (fun q j hj k u => (MomentumTreeData.norm_iteratedFDeriv_treeRootSpectralAmplitude_leSpatial (P := P)) ζ f S q hj k u)
    (lintegral_treeRootSpectralEnvelope_leSpatial J f S hS hK hM hB hf) G
    ((MomentumTreeData.stronglyMeasurable_treeSpatialFrequency (P := P.withRootInput)) F.frequency F.frequency_measurable
      hχ.continuous.measurable R hLp γ δ Q T.timeDomain T.measurableSet_timeDomain S)
    (fun u => integrable_cutoffTriangleIntegral hχ hc
      (R.integrable_linkDensity hLp γ δ
        ((MomentumTreeData.spectralLinksSpatial (P := P.withRootInput)) (spatialFrequencyLinks Q (F.frequency u.2)) u.1.1.2.val u.1.2)
        T.measurableSet_timeDomain T.timeDomain_subset_linkBoxes))
    (ENNReal.mul_lt_top hCphys ENNReal.ofReal_lt_top) hphys
  let Q' := fun u : U × α =>
    (MomentumTreeData.spectralLinksSpatial (P := P.withRootInput)) (spatialFrequencyLinks Q (F.frequency u.2)) u.1.1.2.val u.1.2
  let T' := fun u : U × α => (MomentumTreeData.spectralTreeClockFibersSpatial (P := P.withRootInput))
    (spatialFrequencyLinks Q (F.frequency u.2)) ((TreeClockFibers.spatialFrequency (T := T)) (F.frequency u.2)) u.1.1.2.val u.1.2
  have hJ := T.selection.card_links_le_two (by omega : l + 2 ≤ 4)
  have hdecay := hb L hLa n (incoherenceCount Q) hg (U × α) Q'
    (fun _ => hspan) (fun _ => rfl) T' R T.selection.coordinates.rootLinks hJ
    (fun _ => hfirst) (fun _ => hlast) (fun _ => rfl) (fun _ => hχroot) (fun _ => hχsel)
  change Fourier.mixedFourierNorm η J 0
    (fun t k => ∫ u, F.amplitude u.2 * rootAmplitudeSumSpatial
      ((MomentumTreeData.treeRootSpectralAmplitudeSpatial (P := P)) ζ f S) k u.1 * G t u ∂(sourceCellMeasure S).prod F.μ) ≤ _
  apply hfull.trans
  exact (mul_le_mul' le_rfl hdecay).trans_eq (by ring)

end WaveTurbulence.Flower.IncTop