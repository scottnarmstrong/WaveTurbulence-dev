/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.RootAmplitudeMixture
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.TreeRootSpectralMass
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.AllCellTreeDecay
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.MovingTreeFamily

/-! Ported by source from C2-B-TOP `Cut2BReg.TreeRootSpatialDecay` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.
 # Full spatial derivatives of the actual tree source extension -/

public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- The actual common spectral extension, with the locally finite root partition in its amplitude. -/
@[expose] def MomentumTreeData.rootPartitionSourceTreeExtensionSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (R : RootCoordinates n) (χ : ℝ → ℝ)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  ∫ u, rootAmplitudeSumSpatial ((MomentumTreeData.treeRootSpectralAmplitudeSpatial (P := P)) ζ f S) k u *
    (MomentumTreeData.allCellTreeKernelSpatial (P := P.withRootInput)) R χ L γ δ Q I S t u ∂sourceCellMeasure S

/-- Actual tree derivatives with a uniform root-partition mass and the common causal Fourier bound.
No derivative, integrability or kernel-decay estimates are carrier fields. -/
theorem exists_rootPartitionSourceTreeExtension_boundSpatial (d : ℕ) (hd : 3 ≤ d) :
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
        Fourier.mixedFourierNorm η J 0
          ((MomentumTreeData.rootPartitionSourceTreeExtensionSpatial (P := P)) ζ R χ L γ δ Q T.timeDomain f S) ≤
          (ENNReal.ofReal (rootLocalOverlapConstantSpatial d) *
            (ENNReal.ofReal (treeRootAmplitudeDerivativeFactorSpatial d J) *
              ENNReal.ofReal (maskedSourceSpatialConstantSpatial d (m + 1) J 0) * ENNReal.ofReal (C ^ n) *
                (ENNReal.ofReal (leafMomentLocalizationConstant d J M * treeAugmentedInputBoundSpatial d K M B) ^ (m + 1) *
                  ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n)))) *
            ENNReal.ofReal ((C₀ * δ) ^ n *
              L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_allCellTreeKernel_decaySpatial d hd
  obtain ⟨Cᵣ, _, hr⟩ := exists_rootDensity_L1_bound d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro l hl η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨hc⟩ := Fourier.exists_cutoffControl hχ hcχ
  obtain ⟨L₁, hL₁, hb⟩ := hb l hl η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₂, _, hr⟩ := hr γ hγ η hη hηγ δ hδ D hD
  refine ⟨max L₁ L₂, hL₁.trans (le_max_left _ _), ?_⟩
  intro L hL n m w J K M P Q hspan hg R T hfirst hlast hχroot hχsel f B hK hM hB hf S C hS ζ
  have hLa := (le_max_left L₁ L₂).trans hL
  have hLr := (le_max_right L₁ L₂).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le (hL₁.trans hLa)
  let G := (MomentumTreeData.allCellTreeKernelSpatial (P := P.withRootInput)) R χ L γ δ Q T.timeDomain S
  let Nr := ENNReal.ofReal ((Cᵣ * δ) ^ n *
    L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q))
  let Cphys := Fourier.cutoffKernelL1Factor hc.radius hc.bound * Fourier.localTimeL1Factor 1 hc.radius hc.bound
  have hCphys : Cphys < ⊤ := ENNReal.mul_lt_top (Fourier.cutoffKernelL1Factor_ne_top _ _).lt_top
    (Fourier.localTimeL1Factor_ne_top (le_refl (1 : ℝ)) _ _).lt_top
  have hphys (u : SourceCellIndex S × (LocalizedCellIndex n (m + 1) → Fin d → ℝ)) :
      eLpNorm (fun t => G t u) 1 ≤ Cphys * Nr := by
    apply (eLpNorm_cutoffTriangleIntegral_one_le hχ hc
      (R.integrable_linkDensity hLp γ δ ((MomentumTreeData.spectralLinksSpatial (P := P.withRootInput)) Q u.1.2.val u.2)
        T.measurableSet_timeDomain T.timeDomain_subset_linkBoxes)).trans
    apply mul_le_mul' le_rfl
    exact hr L hLr n ((MomentumTreeData.spectralLinksSpatial (P := P.withRootInput)) Q u.1.2.val u.2) hspan
      T.timeDomain T.measurableSet_timeDomain T.timeDomain_subset_linkBoxes R
  have hfull := mixedFourierNorm_rootAmplitudeMixture_leSpatial (N := J) (sourceCellMeasure S) η
    ((MomentumTreeData.treeRootSpectralAmplitudeSpatial (P := P)) ζ f S) (treeRootSpectralEnvelopeSpatial J f S)
    ((MomentumTreeData.treeRootSpectralAmplitude_eq_zeroSpatial (P := P)) ζ f S)
    (fun q u => ((MomentumTreeData.contDiff_treeRootSpectralAmplitudeSpatial (P := P)) ζ f S q u).of_le (by simp))
    (fun q j _ k => (MomentumTreeData.stronglyMeasurable_treeRootAmplitudeDerivativeSpatial (P := P)) ζ f S (by omega) hf q k j)
    (integrable_treeRootSpectralEnvelopeSpatial J f S hS hK hM hf)
    (measurable_treeRootSpectralEnvelopeSpatial J f S (by omega) hf)
    (treeRootSpectralEnvelope_nonnegSpatial J f S)
    (fun q j hj k u => (MomentumTreeData.norm_iteratedFDeriv_treeRootSpectralAmplitude_leSpatial (P := P)) ζ f S q hj k u)
    (lintegral_treeRootSpectralEnvelope_leSpatial J f S hS hK hM hB hf) G
    ((MomentumTreeData.stronglyMeasurable_allCellTreeKernelSpatial (P := P.withRootInput)) R hχ.continuous.measurable hLp γ δ Q
      T.timeDomain T.measurableSet_timeDomain S)
    (fun u => integrable_cutoffTriangleIntegral hχ hc
      (R.integrable_linkDensity hLp γ δ ((MomentumTreeData.spectralLinksSpatial (P := P.withRootInput)) Q u.1.2.val u.2)
        T.measurableSet_timeDomain T.timeDomain_subset_linkBoxes))
    (ENNReal.mul_lt_top hCphys ENNReal.ofReal_lt_top) hphys
  exact hfull.trans (mul_le_mul' le_rfl
    (hb L hLa n (m + 1) w P.withRootInput Q hspan hg R T hfirst hlast hχroot hχsel S))

end WaveTurbulence.Flower.IncTop