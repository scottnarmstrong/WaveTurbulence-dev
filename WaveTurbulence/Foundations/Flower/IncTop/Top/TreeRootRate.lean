/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Top.RootMixture
public import WaveTurbulence.Foundations.Flower.IncTop.Top.RootJets
public import WaveTurbulence.Foundations.Flower.IncTop.Top.CoupleRootRate
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.WeightedTreeExtension
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.WeightedTreeAgreement
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.TreeCoefficientAbsorption
public import WaveTurbulence.Foundations.Incoh.CoupleLinkCellLocalization

/-! Ported by source from C2-B-TOP `C2BTop.TreeRootRate` (sha256 in COPIED-SHA256SUMS); mechanical edits only.
 # Root-modulated raw trees at the printed Proposition 5.1 rate

C2-B-REG's weighted tree chain (`exists_fourierRootPartitionSourceTreeExtension_bound`,
`exists_rawTreeKernel_upperRestriction_boundFourier`, `exists_weightedRawTreeKernel_XNormRestr_bound`)
for the measure `G.at k`, at the extra cost `rootJetConstant (30d) * G.momentMass (30d)`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff
namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh

/-- C2-B-REG's tree cell constant. -/
def treeCellConstant (d m J K M n : ℕ) (C B : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (rootLocalOverlapConstantSpatial d) *
    (ENNReal.ofReal (treeRootAmplitudeDerivativeFactorSpatial d J) *
      ENNReal.ofReal (maskedSourceSpatialConstantSpatial d (m + 1) J 0) * ENNReal.ofReal (C ^ n) *
        (ENNReal.ofReal (leafMomentLocalizationConstant d J M * treeAugmentedInputBoundSpatial d K M B) ^ (m + 1) *
          ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n)))

/-- The root-modulated tree extension bound. -/
theorem exists_rootTreeExtension_bound (d : ℕ) (hd : 3 ≤ d) :
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
        ∀ {α : Type} [MeasurableSpace α] (G : RootMeasure d n α), G.momentMass J < ⊤ →
        Fourier.mixedFourierNorm η J 0
          (fun t k => (MomentumTreeData.fourierRootPartitionSourceTreeExtension (P := P)) (G.at k) ζ R χ L γ δ Q T.timeDomain f S t k) ≤
          ENNReal.ofReal (rootJetConstant J) * (treeCellConstant d m J K M n C B * G.momentMass J) *
            ENNReal.ofReal ((C₀ * δ) ^ n *
              L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_parameterTreeCausalExtension_decay d hd
  obtain ⟨Cᵣ, _, hr⟩ := exists_rootDensity_L1_bound d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro l hl η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨hc⟩ := Fourier.exists_cutoffControl hχ hcχ
  obtain ⟨L₁, hL₁, hb⟩ := hb l hl η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₂, _, hr⟩ := hr γ hγ η hη hηγ δ hδ D hD
  refine ⟨max L₁ L₂, hL₁.trans (le_max_left _ _), ?_⟩
  intro L hL n m w J K M P Q hspan hg R T hfirst hlast hχroot hχsel f B hK hM hB hf S C hS ζ α _ G hfin
  have hLa := (le_max_left L₁ L₂).trans hL
  have hLr := (le_max_right L₁ L₂).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le (hL₁.trans hLa)
  let U := SourceCellIndex S × (LocalizedCellIndex n (m + 1) → Fin d → ℝ)
  let Kt := fun t (u : U × α) => (MomentumTreeData.allCellTreeKernelSpatial (P := P.withRootInput)) R χ L γ δ
    (spatialFrequencyLinks Q (G.base.frequency u.2)) T.timeDomain S t u.1
  let Nr := ENNReal.ofReal ((Cᵣ * δ) ^ n *
    L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q))
  let Cphys := Fourier.cutoffKernelL1Factor hc.radius hc.bound * Fourier.localTimeL1Factor 1 hc.radius hc.bound
  have hCphys : Cphys < ⊤ := ENNReal.mul_lt_top (Fourier.cutoffKernelL1Factor_ne_top _ _).lt_top
    (Fourier.localTimeL1Factor_ne_top (le_refl (1 : ℝ)) _ _).lt_top
  have hphys (u : U × α) :
      eLpNorm (fun t => Kt t u) 1 ≤ Cphys * Nr := by
    apply (eLpNorm_cutoffTriangleIntegral_one_le hχ hc
      (R.integrable_linkDensity hLp γ δ ((MomentumTreeData.spectralLinksSpatial (P := P.withRootInput))
        (spatialFrequencyLinks Q (G.base.frequency u.2)) u.1.1.2.val u.1.2)
        T.measurableSet_timeDomain T.timeDomain_subset_linkBoxes)).trans
    apply mul_le_mul' le_rfl
    exact hr L hLr n ((MomentumTreeData.spectralLinksSpatial (P := P.withRootInput)) (spatialFrequencyLinks Q (G.base.frequency u.2))
      u.1.1.2.val u.1.2) hspan T.timeDomain T.measurableSet_timeDomain T.timeDomain_subset_linkBoxes R
  have hfull := mixedFourierNorm_rootProductRootMixture_le (N := J) (sourceCellMeasure S) G η
    ((MomentumTreeData.treeRootSpectralAmplitudeSpatial (P := P)) ζ f S) (treeRootSpectralEnvelopeSpatial J f S)
    ((MomentumTreeData.treeRootSpectralAmplitude_eq_zeroSpatial (P := P)) ζ f S)
    (fun q u => ((MomentumTreeData.contDiff_treeRootSpectralAmplitudeSpatial (P := P)) ζ f S q u).of_le (by simp))
    (fun q j _ k => stronglyMeasurable_rootTreeJets P ζ f S G.root_measurable (by omega) hf q k j)
    (integrable_treeRootSpectralEnvelopeSpatial J f S hS hK hM hf)
    (measurable_treeRootSpectralEnvelopeSpatial J f S (by omega) hf)
    (treeRootSpectralEnvelope_nonnegSpatial J f S)
    (fun q j hj k u => (MomentumTreeData.norm_iteratedFDeriv_treeRootSpectralAmplitude_leSpatial (P := P)) ζ f S q hj k u)
    (lintegral_treeRootSpectralEnvelope_leSpatial J f S hS hK hM hB hf) Kt
    ((MomentumTreeData.stronglyMeasurable_treeSpatialFrequency (P := P.withRootInput)) G.base.frequency G.base.frequency_measurable
      hχ.continuous.measurable R hLp γ δ Q T.timeDomain T.measurableSet_timeDomain S)
    (fun u => integrable_cutoffTriangleIntegral hχ hc
      (R.integrable_linkDensity hLp γ δ
        ((MomentumTreeData.spectralLinksSpatial (P := P.withRootInput)) (spatialFrequencyLinks Q (G.base.frequency u.2)) u.1.1.2.val u.1.2)
        T.measurableSet_timeDomain T.timeDomain_subset_linkBoxes))
    (ENNReal.mul_lt_top hCphys ENNReal.ofReal_lt_top) hphys hfin
  let Q' := fun u : U × α =>
    (MomentumTreeData.spectralLinksSpatial (P := P.withRootInput)) (spatialFrequencyLinks Q (G.base.frequency u.2)) u.1.1.2.val u.1.2
  let T' := fun u : U × α => (MomentumTreeData.spectralTreeClockFibersSpatial (P := P.withRootInput))
    (spatialFrequencyLinks Q (G.base.frequency u.2)) ((TreeClockFibers.spatialFrequency (T := T)) (G.base.frequency u.2))
      u.1.1.2.val u.1.2
  have hJ := T.selection.card_links_le_two (by omega : l + 2 ≤ 4)
  have hdecay := hb L hLa n (incoherenceCount Q) hg (U × α) Q'
    (fun _ => hspan) (fun _ => rfl) T' R T.selection.coordinates.rootLinks hJ
    (fun _ => hfirst) (fun _ => hlast) (fun _ => rfl) (fun _ => hχroot) (fun _ => hχsel)
  change Fourier.mixedFourierNorm η J 0
    (fun t k => ∫ u, (G.at k).amplitude u.2 * rootAmplitudeSumSpatial
      ((MomentumTreeData.treeRootSpectralAmplitudeSpatial (P := P)) ζ f S) k u.1 * Kt t u ∂(sourceCellMeasure S).prod G.base.μ) ≤ _
  apply hfull.trans
  refine (mul_le_mul' le_rfl hdecay).trans_eq ?_
  unfold treeCellConstant
  ring

/-- Root-modulated tree restriction estimate. -/
theorem exists_rootRawTreeKernel_restriction_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ Cₗ : ℝ, 0 < Cₗ ∧ ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ l : ℕ, l ≤ 2 →
      ∀ η : ℝ, 0 < η → η ≤ 1 / 100 →
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
        ∀ E : Set (Fin 2 → ℝ), (∀ t ∈ E, t 1 ≤ t 0) →
        (∀ t ∈ E, ∀ j, χ (t j) = 1) → ∀ ζ : Circle, ∀ A : Set (Mom d),
        ∀ {α : Type} [MeasurableSpace α] (G : RootMeasure d n α), G.momentMass J < ⊤ →
        Fourier.mixedRestrictionNorm η J 0 E A
          (fun t k => (MomentumTreeData.weightedSourceTreeKernel (P := P)) (G.at k) ζ R L γ δ Q T.timeDomain f t k) ≤
          ENNReal.ofReal (rootJetConstant J) * (treeCellConstant d m J K M n Cₗ B * G.momentMass J) *
          ENNReal.ofReal ((C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q)) := by
  obtain ⟨Cₗ, hCₗ, hloc⟩ := exists_uniform_couple_link_cell_localization d (by omega)
  obtain ⟨C₀, hC₀, hb⟩ := exists_rootTreeExtension_bound d hd
  obtain ⟨Cᵣ, _, hr⟩ := exists_rootDensity_L1_bound d hd
  refine ⟨Cₗ, hCₗ, C₀, hC₀, ?_⟩
  intro l hl η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨hc⟩ := Fourier.exists_cutoffControl hχ hcχ
  obtain ⟨L₁, hL₁, hb⟩ := hb l hl η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₂, _, hr⟩ := hr γ hγ η hη hηγ δ hδ D hD
  refine ⟨max L₁ L₂, hL₁.trans (le_max_left _ _), ?_⟩
  intro L hL n m w J K M P Q hspan hg R T hfirst hlast hχroot hχsel f B hK hM hB hf E hforward hχext ζ A
    α _ G hfin
  have hLa := (le_max_left L₁ L₂).trans hL
  have hLr := (le_max_right L₁ L₂).trans hL
  have hLone : 1 ≤ L := hL₁.trans hLa
  choose S hScard hcover using (fun c => hloc n (m + 1) w P.withRootInput P.withRootInput_all_leaves c)
  have hroot (z : (Fin n × Fin 2) → Fin d → ℤ) (ξ : LocalizedCellIndex n (m + 1) → Fin d → ℝ) (a : α) :
      eLpNorm (R.linkDensity L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P.withRootInput))
        (spatialFrequencyLinks Q (G.base.frequency a)) z ξ) T.timeDomain) 1 ≤
      ENNReal.ofReal ((Cᵣ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q)) := by
    simpa only [(MomentumTreeData.incoherenceCount_spectralLinksSpatial (P := P.withRootInput)),
      incoherenceCount_spatialFrequencyLinks] using
      hr L hLr n ((MomentumTreeData.spectralLinksSpatial (P := P.withRootInput)) (spatialFrequencyLinks Q (G.base.frequency a)) z ξ)
        hspan T.timeDomain T.measurableSet_timeDomain T.timeDomain_subset_linkBoxes R
  have hagree (t : E) (k : A) :
      (MomentumTreeData.fourierRootPartitionSourceTreeExtension (P := P)) (G.at k) ζ R χ L γ δ Q T.timeDomain f S t k =
        (MomentumTreeData.weightedSourceTreeKernel (P := P)) (G.at k) ζ R L γ δ Q T.timeDomain f t k :=
    (MomentumTreeData.fourierRootPartitionSourceTreeExtension_agrees_on_cutoff (P := P)) (G.at k) ζ R hχ hc L γ δ Q T.timeDomain
      T.measurableSet_timeDomain T.timeDomain_subset_linkBoxes hχroot f S hcover hScard
      hLone (by omega) hM hf ENNReal.ofReal_lt_top hroot t (hχext t t.property) (hforward t t.property) k
  apply (Fourier.mixedRestrictionNorm_le_extension
    (fun t k => (MomentumTreeData.fourierRootPartitionSourceTreeExtension (P := P)) (G.at k) ζ R χ L γ δ Q T.timeDomain f S t k)
      hagree).trans
  exact hb L hLa n m w J K M P Q hspan hg R T hfirst hlast hχroot hχsel f B hK hM hB hf S Cₗ hScard ζ G hfin

/-- Root-modulated raw tree, printed rate (`30d, 0`). -/
theorem exists_rootRawTreeKernel_rate (d : ℕ) (hd : 3 ≤ d) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ l : ℕ, l ≤ 2 → ∀ η : ℝ, 0 < η → η ≤ 1 / 100 →
      (100 * (d : ℝ)) ^ 2 * η ≤ 1 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n m w : ℕ, m + 1 ≤ 3 * n →
        ∀ P : MomentumTreeData n m w, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        1 ≤ incoherenceCount Q → ∀ R : RootCoordinates n, ∀ T : TreeClockFibers l Q,
        R.rootVertex 0 = T.selection.coordinates.rootVertex 0 →
        R.rootVertex 1 = T.selection.coordinates.rootVertex (Fin.last (l + 1)) →
        (∀ v ∈ R.rootBox Q, ∀ j, χ (v j) = 1) →
        (∀ v ∈ T.selection.coordinates.rootBox Q, ∀ j, χ (v j) = 1) →
        ∀ f : Fin m → Mom d → ℂ,
        (∀ a, Fourier.spatialNorm (40 * d) (40 * d) (f a) ≤ ENNReal.ofReal B) →
        ∀ E : Set (Fin 2 → ℝ), (∀ t ∈ E, t 1 ≤ t 0) →
        (∀ t ∈ E, ∀ j, χ (t j) = 1) → ∀ ζ : Circle, ∀ A : Set (Mom d),
        ∀ {α : Type} [MeasurableSpace α] (G : RootMeasure d n α),
        Fourier.mixedRestrictionNorm η (30 * d) 0 E A
          (fun t k => (MomentumTreeData.weightedSourceTreeKernel (P := P)) (G.at k) ζ R L γ δ Q T.timeDomain f t k) ≤
            ENNReal.ofReal (rootJetConstant (30 * d)) * G.momentMass (30 * d) *
            ENNReal.ofReal ((C₁ * δ) ^ n *
              L ^ (-(incoherenceExponent d γ - Real.sqrt η) * incoherenceCount Q)) := by
  obtain ⟨Cₗ, hCₗ, C₀, hC₀, hb⟩ := exists_rootRawTreeKernel_restriction_bound d hd
  let C₁ := treeSourceExponentialCoefficientSpatial d (30 * d) (40 * d) (40 * d) B Cₗ * C₀
  have hC₁ : 0 < C₁ := mul_pos (treeSourceExponentialCoefficient_posSpatial _ _ _ _ _ _) hC₀
  refine ⟨C₁, hC₁, ?_⟩
  intro l hl η hη hη₁ hsmall χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb l hl η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n m w hm P Q hspan hg R T hfirst hlast hχroot hχsel f hf E hforward hχext ζ A α _ G
  have hn := one_le_linkCount_of_incoherent Q hg
  have hLone := hL₀.trans hL
  have hrate : 0 < (C₁ * δ) ^ n *
      L ^ (-(incoherenceExponent d γ - Real.sqrt η) * incoherenceCount Q) :=
    mul_pos (pow_pos (mul_pos hC₁ hδ) _) (Real.rpow_pos_of_pos (zero_lt_one.trans_le hLone) _)
  by_cases hfin : G.momentMass (30 * d) = ⊤
  · exact le_top_of_momentMass_top G _ hfin (rootJetConstant_pos _) hrate _
  have hraw := hb L hL n m w (30 * d) (40 * d) (40 * d) P Q hspan hg R T hfirst hlast
    hχroot hχsel f B (by omega) (by omega) hB hf E hforward hχext ζ A G (lt_top_iff_ne_top.mpr hfin)
  apply hraw.trans
  have habs : treeCellConstant d m (30 * d) (40 * d) (40 * d) n Cₗ B * ENNReal.ofReal ((C₀ * δ) ^ n *
      L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q)) ≤
      ENNReal.ofReal ((C₁ * δ) ^ n *
        L ^ (-(incoherenceExponent d γ - Real.sqrt η) * incoherenceCount Q)) := by
    apply (tree_source_ennreal_coefficient_leSpatial hn hm hCₗ.le hC₀.le hδ.le
      (Real.rpow_nonneg (zero_le_one.trans hLone) _)).trans
    apply ENNReal.ofReal_le_ofReal
    change (C₁ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q) ≤ _
    exact mul_le_mul_of_nonneg_left (incoherence_rpow_le_sqrt_loss hLone hη.le hsmall)
      (pow_nonneg (mul_nonneg hC₁.le hδ.le) _)
  calc
    _ = ENNReal.ofReal (rootJetConstant (30 * d)) * G.momentMass (30 * d) *
        (treeCellConstant d m (30 * d) (40 * d) (40 * d) n Cₗ B * ENNReal.ofReal ((C₀ * δ) ^ n *
          L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q))) := by ring
    _ ≤ _ := mul_le_mul' le_rfl habs

end WaveTurbulence.Flower.IncTop