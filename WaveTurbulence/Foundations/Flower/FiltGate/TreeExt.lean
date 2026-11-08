/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltSrc.SpectralMeas
public import WaveTurbulence.Foundations.Flower.FiltSrc.Spectral
public import WaveTurbulence.Foundations.Flower.FiltSrc.Cells
public import WaveTurbulence.Foundations.Flower.FiltSrc.Source
public import WaveTurbulence.Foundations.Flower.FiltProd.Cumul
public import WaveTurbulence.Foundations.Flower.FiltProd.Dens
public import WaveTurbulence.Foundations.Flower.IncTop.Top.TreeRootRate

/-! # D5b-3 FILT-GATE: the filtered tree extensions, their agreement and root-mixture bound at any weight `θ`

Twins (copied by source from INC-TOP, sha256 in COPIED-SHA256SUMS; `φ` inserted after the links):
- `Reg/MaskedTreePointwise`: `allCellMaskedSourceTreeExtensionSpatialFilt`,
  `integrable_allCellMaskedTreeSlice_of_uniformRootL1SpatialFilt`, `allCellMaskedSourceTreeExtension_eq_tsumSpatialFilt`;
- `Reg/MovingTreeFamily.unrestrictedTreeKernelSpatial`, `Reg/TreeUpperBoxAgreement`:
  `unrestrictedTreeKernelSpatialFilt`, `unrestrictedTreeKernel_agrees_on_cutoffSpatialFilt`;
- `Reg/MaskedRawTreeUpperAgreement`: `allCellMaskedSourceTreeExtension_agrees_on_cutoffSpatialFilt`;
- `Reg/TreeRootPartition`: `hasSum_sourceTreeKernel_rootPartitionSpatialFilt`;
- `Reg/TreeRootSpatialDecay.rootPartitionSourceTreeExtensionSpatial`, `Reg/TreeRootUpperAgreement`:
  `rootPartitionSourceTreeExtensionSpatialFilt`, `rootPartitionSourceTreeExtension_agrees_on_cutoffSpatialFilt`;
- `Reg/WeightedTreeExtension.fourierRootPartitionSourceTreeExtension`, `Reg/WeightedTreeAgreement`:
  `fourierRootPartitionSourceTreeExtensionFilt`, `fourierRootPartitionSourceTreeExtension_agrees_on_cutoffFilt`;
- the body of `Top/TreeRootRate.exists_rootTreeExtension_bound` with the time weight `θ` free
  (`rootTreeExtensionFilt_le_of_roots`): the bound is the cell constant times the `X^θ` norm of the spectral family. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.FiltGate
open WaveTurbulence.Incoh WaveTurbulence.Flower.IncTop WaveTurbulence.Flower.FiltSrc
  WaveTurbulence.Flower.FiltProd

/-- The filtered masked tree extension on the fixed source-cell measure. -/
def MomentumTreeData.allCellMaskedSourceTreeExtensionSpatialFilt {d n m w : ℕ}
    (P : MomentumTreeData n m w) (χ : ℝ → ℝ) (ζ : Circle) (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (I : Set (Fin n → Fin 2 → ℝ))
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  ∫ u, (MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S k u *
    (MomentumTreeData.allCellTreeKernelSpatialFilt (P := P)) R χ L γ δ Q φ I S t u ∂sourceCellMeasure S

/-- Conditional pointwise Fubini typing from the root-marginal bound (filtered trees). -/
theorem MomentumTreeData.integrable_allCellMaskedTreeSlice_of_uniformRootL1SpatialFilt {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : Fourier.CutoffControl χ) (ζ : Circle) (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (I : Set (Fin n → Fin 2 → ℝ))
    (hI : MeasurableSet I) (hbox : I ⊆ Set.univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hL : 0 < L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    {N : ℝ≥0∞} (hN : N < ⊤)
    (hb : ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ ξ : LocalizedCellIndex n m → Fin d → ℝ,
      eLpNorm (RootCoordinates.linkDensityFilt R L γ δ
        ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z ξ) φ I) 1 ≤ N)
    (t : Fin 2 → ℝ) (k : Mom d) :
    Integrable (fun u => (MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S k u *
      (MomentumTreeData.allCellTreeKernelSpatialFilt (P := P)) R χ L γ δ Q φ I S t u) (sourceCellMeasure S) := by
  have hKs : StronglyMeasurable ((MomentumTreeData.allCellTreeKernelSpatialFilt (P := P)) R χ L γ δ Q φ I S t) :=
    ((MomentumTreeData.stronglyMeasurable_allCellTreeKernelSpatialFilt (P := P)) R hχ.continuous.measurable hL
      γ δ Q φ I hI S).comp_measurable (g := fun u => (t, u)) (measurable_const.prodMk measurable_id)
  apply integrable_mul_of_uniform_enorm_bound (sourceCellMeasure S)
    ((MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S k)
    ((MomentumTreeData.allCellTreeKernelSpatialFilt (P := P)) R χ L γ δ Q φ I S t)
    ((MomentumTreeData.integrable_allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S hS hK hM hB h k)
    hKs.aestronglyMeasurable
    (N := ENNReal.ofReal hc.bound ^ 4 * N) (ENNReal.mul_lt_top (by finiteness) hN)
  intro u
  exact (enorm_cutoffTriangleIntegral_le hχ hc
    (RootCoordinates.integrable_linkDensityFilt R hL γ δ
      ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.1.2.val u.2) φ hI hbox) t).trans
    (mul_le_mul' le_rfl (hb _ _))

/-- The filtered masked tree extension is the sum of its cell spectral integrals. -/
theorem MomentumTreeData.allCellMaskedSourceTreeExtension_eq_tsumSpatialFilt {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : Fourier.CutoffControl χ) (ζ : Circle) (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (I : Set (Fin n → Fin 2 → ℝ))
    (hI : MeasurableSet I) (hbox : I ⊆ Set.univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hL : 0 < L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    {N : ℝ≥0∞} (hN : N < ⊤)
    (hb : ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ ξ : LocalizedCellIndex n m → Fin d → ℝ,
      eLpNorm (RootCoordinates.linkDensityFilt R L γ δ
        ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z ξ) φ I) 1 ≤ N)
    (t : Fin 2 → ℝ) (k : Mom d) :
    (MomentumTreeData.allCellMaskedSourceTreeExtensionSpatialFilt (P := P)) χ ζ R L γ δ Q φ I f S t k =
      ∑' u : SourceCellIndex S, ∫ ξ : LocalizedCellIndex n m → Fin d → ℝ,
        (MomentumTreeData.maskedSourceSpectralAmplitudeSpatial (P := P)) ζ f u.1 u.2.val k ξ *
          Fourier.cutoffTriangleIntegral χ (RootCoordinates.linkDensityFilt R L γ δ
            ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.2.val ξ) φ I) t := by
  have hs := (MomentumTreeData.integrable_allCellMaskedTreeSlice_of_uniformRootL1SpatialFilt (P := P)) hχ hc ζ R
    L γ δ Q φ I hI hbox f S hS hL hK hM hB h hN hb t k
  change Integrable (fun u => (MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S k u *
    (MomentumTreeData.allCellTreeKernelSpatialFilt (P := P)) R χ L γ δ Q φ I S t u)
      (Measure.count.prod volume) at hs
  change (∫ u, (MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S k u *
    (MomentumTreeData.allCellTreeKernelSpatialFilt (P := P)) R χ L γ δ Q φ I S t u
      ∂(Measure.count.prod volume)) = _
  rw [integral_prod _ hs, integral_countable hs.integral_prod_left]
  simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
  rfl

/-- The filtered causal spectral link kernel on the fixed unrestricted cell measure. -/
def MomentumTreeData.unrestrictedTreeKernelSpatialFilt {d n m w : ℕ}
    (P : MomentumTreeData n m w) (R : RootCoordinates n) (χ : ℝ → ℝ) (L γ δ : ℝ)
    (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (I : Set (Fin n → Fin 2 → ℝ))
    (t : Fin 2 → ℝ) (u : UnrestrictedCellIndex d n m × (LocalizedCellIndex n m → Fin d → ℝ)) : ℂ :=
  Fourier.cutoffTriangleIntegral χ (RootCoordinates.linkDensityFilt R L γ δ
    ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.1.2 u.2) φ I) t

/-- The filtered spectral tree kernel equals the literal normalized causal source on its external box. -/
theorem MomentumTreeData.unrestrictedTreeKernel_agrees_on_cutoffSpatialFilt {d n m w : ℕ}
    (P : MomentumTreeData n m w) (R : RootCoordinates n) {χ : ℝ → ℝ}
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (I : Set (Fin n → Fin 2 → ℝ))
    (hI : MeasurableSet I) (hbox : I ⊆ univ.pi (fun i => linkBox (Q i)))
    (hχ : ∀ a ∈ R.rootBox Q, ∀ j, χ (a j) = 1) (hL : 0 < L)
    (t : Fin 2 → ℝ) (ht : ∀ j, χ (t j) = 1) (hord : t 1 ≤ t 0)
    (u : UnrestrictedCellIndex d n m × (LocalizedCellIndex n m → Fin d → ℝ)) :
    (MomentumTreeData.unrestrictedTreeKernelSpatialFilt (P := P)) R χ L γ δ Q φ I t u =
      normalizedLinkIntegralFilt L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.1.2 u.2) φ
        (I ∩ R.causalRootCut t) := by
  have he := RootCoordinates.treeCausalExtension_eq_weighted_sourceFilt R hL γ δ
    (fun _ : Mom d => (MomentumTreeData.spectralLinksSpatial (P := P)) Q u.1.2 u.2) (fun _ => φ) (fun _ => I) 0
    hI hbox hχ hord
  change Fourier.cutoffTriangleIntegral χ (RootCoordinates.linkDensityFilt R L γ δ
    ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.1.2 u.2) φ I) t = _ at he
  change Fourier.cutoffTriangleIntegral χ (RootCoordinates.linkDensityFilt R L γ δ
    ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.1.2 u.2) φ I) t =
    RootCoordinates.causalKernelFilt R L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.1.2 u.2) φ I t
  simpa only [ht 0, ht 1, Complex.ofReal_one, one_mul] using he

/-- The filtered masked tree extension agrees with the unlocalized filtered source on the whole root box. -/
theorem MomentumTreeData.allCellMaskedSourceTreeExtension_agrees_on_cutoffSpatialFilt {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : Fourier.CutoffControl χ) (Croot : RootInputCoordinates P) (ζ : Circle)
    (R : RootCoordinates n) (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    {Bφ : ℝ} (hφ : ∀ i u, ‖φ i u‖ ≤ Bφ) (I : Set (Fin n → Fin 2 → ℝ))
    (hI : MeasurableSet I) (hbox : I ⊆ Set.univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, P.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin n × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hL : 1 ≤ L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    {N : ℝ≥0∞} (hN : N < ⊤)
    (hb : ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ ξ : LocalizedCellIndex n m → Fin d → ℝ,
      eLpNorm (RootCoordinates.linkDensityFilt R L γ δ
        ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z ξ) φ I) 1 ≤ N)
    (hχroot : ∀ a ∈ R.rootBox Q, ∀ j, χ (a j) = 1)
    (t : Fin 2 → ℝ) (ht : ∀ j, χ (t j) = 1) (hord : t 1 ≤ t 0) (k : Mom d) :
    (MomentumTreeData.allCellMaskedSourceTreeExtensionSpatialFilt (P := P)) χ ζ R L γ δ Q φ I f S t k =
      (MomentumTreeData.sourceTreeKernelSpatialFilt (P := P)) ζ R L γ δ Q φ I f t k := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  rw [(MomentumTreeData.allCellMaskedSourceTreeExtension_eq_tsumSpatialFilt (P := P)) hχ hc ζ R L γ δ Q φ I
    hI hbox f S hS hLp hK hM hB h hN hb]
  unfold MomentumTreeData.sourceTreeKernelSpatialFilt
  rw [(MomentumTreeData.sourceIntegral_eq_tsum_localizedSourceIntegralSpatialFilt (P := P)) ζ L γ δ Q φ hφ
    (I ∩ R.causalRootCut t) (Set.inter_subset_left.trans hbox) f S hcover hS hL hK hM hB h k]
  apply tsum_congr
  intro u
  rw [← (RootInputCoordinates.sourceRootMask_mul_localizedSourceIntegralSpatialFilt (C := Croot)) ζ L γ δ Q φ
    (I ∩ R.causalRootCut t) f u.1 u.2.val k]
  rw [(MomentumTreeData.localizedSourceIntegral_eq_linkKernelMixtureSpatialFilt (P := P)) ζ L γ δ Q φ
    (I ∩ R.causalRootCut t) (Set.inter_subset_left.trans hbox) f u.1 u.2.val hLp hK hB h k]
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro ξ
  have he := (MomentumTreeData.unrestrictedTreeKernel_agrees_on_cutoffSpatialFilt (P := P)) R L γ δ Q φ I hI hbox
    hχroot hLp t ht hord ((u.1, u.2.val), ξ)
  change Fourier.cutoffTriangleIntegral χ (RootCoordinates.linkDensityFilt R L γ δ
    ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.2.val ξ) φ I) t = _ at he
  dsimp only
  rw [he]
  simp only [MomentumTreeData.maskedSourceSpectralAmplitudeSpatial]
  ring

/-- Exact filtered raw tree source decomposition, with the temporary root input removed by summation. -/
theorem MomentumTreeData.hasSum_sourceTreeKernel_rootPartitionSpatialFilt {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (I : Set (Fin n → Fin 2 → ℝ))
    (f : Fin m → Mom d → ℂ) (t : Fin 2 → ℝ) (k : Mom d) :
    HasSum (fun q : Fin d → ℤ => treeRootCutoffSpatial q k *
      (MomentumTreeData.sourceTreeKernelSpatialFilt (P := P.withRootInput)) ζ R L γ δ Q φ I
        (appendRootInputSpatial f (treeRootPartitionSpatial q)) t k)
      ((MomentumTreeData.sourceTreeKernelSpatialFilt (P := P)) ζ R L γ δ Q φ I f t k) := by
  have hs := (hasSum_treeRootPartitionSpatial k).mul_left
    ((MomentumTreeData.sourceTreeKernelSpatialFilt (P := P)) ζ R L γ δ Q φ I f t k)
  simp only [mul_one] at hs
  convert hs using 1
  funext q
  rw [(MomentumTreeData.sourceTreeKernel_withRootInputSpatialFilt (P := P))]
  calc
    _ = (MomentumTreeData.sourceTreeKernelSpatialFilt (P := P)) ζ R L γ δ Q φ I f t k *
        (treeRootCutoffSpatial q k * treeRootPartitionSpatial q k) := by ring
    _ = _ := by rw [treeRootCutoff_mul_partitionSpatial]

/-- The filtered common spectral extension, with the locally finite root partition in its amplitude. -/
def MomentumTreeData.rootPartitionSourceTreeExtensionSpatialFilt {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (R : RootCoordinates n) (χ : ℝ → ℝ)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (I : Set (Fin n → Fin 2 → ℝ))
    (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  ∫ u, rootAmplitudeSumSpatial ((MomentumTreeData.treeRootSpectralAmplitudeSpatial (P := P)) ζ f S) k u *
    (MomentumTreeData.allCellTreeKernelSpatialFilt (P := P.withRootInput)) R χ L γ δ Q φ I S t u ∂sourceCellMeasure S

/-- The filtered tree extension equals the literal filtered source on the whole forward source domain. -/
theorem MomentumTreeData.rootPartitionSourceTreeExtension_agrees_on_cutoffSpatialFilt {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (R : RootCoordinates n)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : Fourier.CutoffControl χ)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    {Bφ : ℝ} (hφ : ∀ i u, ‖φ i u‖ ≤ Bφ) (I : Set (Fin n → Fin 2 → ℝ))
    (hI : MeasurableSet I) (hbox : I ⊆ univ.pi (fun i => linkBox (Q i)))
    (hχroot : ∀ a ∈ R.rootBox Q, ∀ j, χ (a j) = 1)
    (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, P.withRootInput.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin n × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hL : 1 ≤ L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    {N : ℝ≥0∞} (hN : N < ⊤)
    (hb : ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ ξ : LocalizedCellIndex n (m + 1) → Fin d → ℝ,
      eLpNorm (RootCoordinates.linkDensityFilt R L γ δ
        ((MomentumTreeData.spectralLinksSpatial (P := P.withRootInput)) Q z ξ) φ I) 1 ≤ N)
    (t : Fin 2 → ℝ) (ht : ∀ j, χ (t j) = 1) (hord : t 1 ≤ t 0) (k : Mom d) :
    (MomentumTreeData.rootPartitionSourceTreeExtensionSpatialFilt (P := P)) ζ R χ L γ δ Q φ I f S t k =
      (MomentumTreeData.sourceTreeKernelSpatialFilt (P := P)) ζ R L γ δ Q φ I f t k := by
  classical
  let A := (MomentumTreeData.treeRootSpectralAmplitudeSpatial (P := P)) ζ f S
  let G := (MomentumTreeData.allCellTreeKernelSpatialFilt (P := P.withRootInput)) R χ L γ δ Q φ I S t
  have hi (q : Fin d → ℤ) : Integrable (fun u => A q k u * G u) (sourceCellMeasure S) := by
    obtain ⟨Bq, hBq, hq⟩ := exists_spatialNorm_bound_appendRootPartitionSpatial f hf q
    have h := (MomentumTreeData.integrable_allCellMaskedTreeSlice_of_uniformRootL1SpatialFilt
      (P := P.withRootInput)) hχ hc ζ R L γ δ Q φ I hI hbox (appendRootInputSpatial f (treeRootPartitionSpatial q))
      S hS (zero_lt_one.trans_le hL) hK hM hBq.le hq hN hb t k
    simpa only [A, MomentumTreeData.treeRootSpectralAmplitudeSpatial,
      MomentumTreeData.rootCutoffSpectralAmplitudeSpatial, mul_assoc, G] using
      h.const_mul (treeRootCutoffSpatial q k)
  have hloc := (rootAmplitudeSum_eventuallyEq_modelSpatial A
    ((MomentumTreeData.treeRootSpectralAmplitude_eq_zeroSpatial (P := P)) ζ f S) k).self_of_nhds
  have he : (MomentumTreeData.rootPartitionSourceTreeExtensionSpatialFilt (P := P)) ζ R χ L γ δ Q φ I f S t k =
      ∑ q ∈ rootLocalCoverSpatial k, treeRootCutoffSpatial q k *
        (MomentumTreeData.sourceTreeKernelSpatialFilt (P := P.withRootInput)) ζ R L γ δ Q φ I
          (appendRootInputSpatial f (treeRootPartitionSpatial q)) t k := by
    unfold MomentumTreeData.rootPartitionSourceTreeExtensionSpatialFilt
    change (∫ u, rootAmplitudeSumSpatial A k u * G u ∂sourceCellMeasure S) = _
    have hfun : (fun u => rootAmplitudeSumSpatial A k u * G u) =
        fun u => ∑ q ∈ rootLocalCoverSpatial k, A q k u * G u := by
      funext u
      rw [hloc u]
      exact Finset.sum_mul _ _ _
    rw [hfun, integral_finsetSum _ (fun q _ => hi q)]
    apply Finset.sum_congr rfl
    intro q _
    obtain ⟨Bq, hBq, hq⟩ := exists_spatialNorm_bound_appendRootPartitionSpatial f hf q
    change (∫ u, (treeRootCutoffSpatial q k *
      (MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P.withRootInput)) ζ
        (appendRootInputSpatial f (treeRootPartitionSpatial q)) S k u) * G u ∂sourceCellMeasure S) = _
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    congr 1
    exact (MomentumTreeData.allCellMaskedSourceTreeExtension_agrees_on_cutoffSpatialFilt (P := P.withRootInput))
      hχ hc P.withRootInputCoordinates ζ R L γ δ Q φ hφ I hI hbox _ S hcover hS hL hK hM hBq.le hq hN hb hχroot
      t ht hord k
  rw [he]
  have hs := (MomentumTreeData.hasSum_sourceTreeKernel_rootPartitionSpatialFilt (P := P)) ζ R L γ δ Q φ I f t k
  have hz (q : Fin d → ℤ) (hq : q ∉ rootLocalCoverSpatial k) :
      treeRootCutoffSpatial q k * (MomentumTreeData.sourceTreeKernelSpatialFilt (P := P.withRootInput)) ζ R L γ δ Q φ
        I (appendRootInputSpatial f (treeRootPartitionSpatial q)) t k = 0 := by
    rw [treeRootCutoff_eq_zero_on_ball_of_notMemSpatial k q hq (by simp), zero_mul]
  exact (hasSum_sum_of_ne_finset_zero hz).unique hs

/-- The common filtered tree extension on the product source/character measure. -/
def MomentumTreeData.fourierRootPartitionSourceTreeExtensionFilt {d n m w : ℕ} {α : Type}
    [MeasurableSpace α] (P : MomentumTreeData n m w) (F : Cut2A.SpatialMeasure (PairedMomentum d n) α)
    (ζ : Circle) (R : RootCoordinates n) (χ : ℝ → ℝ) (L γ δ : ℝ)
    (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (I : Set (Fin n → Fin 2 → ℝ)) (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  ∫ u, F.amplitude u.2 * rootAmplitudeSumSpatial ((MomentumTreeData.treeRootSpectralAmplitudeSpatial (P := P)) ζ f S) k u.1 *
    (MomentumTreeData.allCellTreeKernelSpatialFilt (P := P.withRootInput)) R χ L γ δ
      (spatialFrequencyLinks Q (F.frequency u.2)) φ I S t u.1 ∂(sourceCellMeasure S).prod F.μ

/-- Pointwise agreement of the common filtered tree extension and the weighted raw tree. -/
theorem MomentumTreeData.fourierRootPartitionSourceTreeExtension_agrees_on_cutoffFilt
    {d n m w K M : ℕ} {α : Type} [MeasurableSpace α]
    (P : MomentumTreeData n m w) (F : Cut2A.SpatialMeasure (PairedMomentum d n) α)
    (ζ : Circle) (R : RootCoordinates n) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : Fourier.CutoffControl χ)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    {Bφ : ℝ} (hφ : ∀ i u, ‖φ i u‖ ≤ Bφ) (I : Set (Fin n → Fin 2 → ℝ))
    (hI : MeasurableSet I) (hbox : I ⊆ univ.pi (fun i => linkBox (Q i)))
    (hχroot : ∀ v ∈ R.rootBox Q, ∀ j, χ (v j) = 1)
    (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, P.withRootInput.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin n × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    {C B : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n)
    (hL : 1 ≤ L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    {N : ℝ≥0∞} (hN : N < ⊤)
    (hroot : ∀ z ξ a, eLpNorm (RootCoordinates.linkDensityFilt R L γ δ
      ((MomentumTreeData.spectralLinksSpatial (P := P.withRootInput)) (spatialFrequencyLinks Q (F.frequency a)) z ξ)
        φ I) 1 ≤ N)
    (t : Fin 2 → ℝ) (ht : ∀ j, χ (t j) = 1) (hord : t 1 ≤ t 0) (k : Mom d) :
    (MomentumTreeData.fourierRootPartitionSourceTreeExtensionFilt (P := P)) F ζ R χ L γ δ Q φ I f S t k =
      (MomentumTreeData.weightedSourceTreeKernelFilt (P := P)) F ζ R L γ δ Q φ I f t k := by
  have hLp := zero_lt_one.trans_le hL
  let A := rootAmplitudeSumSpatial ((MomentumTreeData.treeRootSpectralAmplitudeSpatial (P := P)) ζ f S) k
  let G := fun u : (SourceCellIndex S × (LocalizedCellIndex n (m + 1) → Fin d → ℝ)) × α =>
    (MomentumTreeData.allCellTreeKernelSpatialFilt (P := P.withRootInput)) R χ L γ δ
      (spatialFrequencyLinks Q (F.frequency u.2)) φ I S t u.1
  have hmG := ((MomentumTreeData.stronglyMeasurable_treeSpatialFrequencyFilt (P := P.withRootInput)) F.frequency
    F.frequency_measurable hχ.continuous.measurable R hLp γ δ Q φ I hI S).comp_measurable
      (g := fun u => (t, u)) (measurable_const.prodMk measurable_id)
  have hiA := (MomentumTreeData.integrable_treeRootAmplitudeSum (P := P)) ζ f S hS hK hM hf k
  have hb (u : (SourceCellIndex S × (LocalizedCellIndex n (m + 1) → Fin d → ℝ)) × α) :
      ‖G u‖ₑ ≤ ENNReal.ofReal hc.bound ^ 4 * N :=
    (enorm_cutoffTriangleIntegral_le hχ hc
      (RootCoordinates.integrable_linkDensityFilt R hLp γ δ
        ((MomentumTreeData.spectralLinksSpatial (P := P.withRootInput)) (spatialFrequencyLinks Q (F.frequency u.2))
          u.1.1.2.val u.1.2) φ hI hbox) t).trans (mul_le_mul' le_rfl (hroot u.1.1.2.val u.1.2 u.2))
  have he := integral_product_amplitude_kernel (sourceCellMeasure S) F A hiA G hmG.aestronglyMeasurable
    (ENNReal.mul_lt_top (by finiteness) hN) hb
  rw [(MomentumTreeData.weightedSourceTreeKernelFilt_eq_integral_of_summable (P := P)) F ζ R L γ δ Q φ hφ I hbox
    f k ((MomentumTreeData.summable_norm_treeLeafWeight_lattice (P := P)) f S hcover hS hL hK hM hf k)]
  unfold MomentumTreeData.fourierRootPartitionSourceTreeExtensionFilt
  rw [he]
  apply integral_congr_ae
  apply ae_of_all
  intro a
  dsimp only
  apply congrArg (fun z : ℂ => F.amplitude a * z)
  exact (MomentumTreeData.rootPartitionSourceTreeExtension_agrees_on_cutoffSpatialFilt (P := P)) ζ R hχ hc L γ δ
    (spatialFrequencyLinks Q (F.frequency a)) φ hφ I hI hbox hχroot f S hcover hS hL hK hM hf
    hN (fun z ξ => hroot z ξ a) t ht hord k

/-- **The root-modulated filtered tree extension bound at any time weight `θ`**: the cell constant times the
`X^θ` norm (`mixedFourierNorm00`) of the spectral kernel family, from a uniform physical root bound `N < ⊤`. -/
theorem rootTreeExtensionFilt_le_of_roots {d n m w J K M : ℕ}
    (P : MomentumTreeData n m w) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : Fourier.CutoffControl χ)
    (R : RootCoordinates n) {L : ℝ} (hLp : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (I : Set (Fin n → Fin 2 → ℝ)) (hI : MeasurableSet I) (hbox : I ⊆ univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ) {B : ℝ} (hK : d + 1 + J ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ)) {C : ℝ}
    (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) (ζ : Circle)
    {α : Type} [MeasurableSpace α] (G : RootMeasure d n α) (hfin : G.momentMass J < ⊤) (θ : ℝ)
    {N : ℝ≥0∞} (hN : N < ⊤)
    (hroot : ∀ (z : (Fin n × Fin 2) → Fin d → ℤ) (ξ : LocalizedCellIndex n (m + 1) → Fin d → ℝ) (a : α),
      eLpNorm (RootCoordinates.linkDensityFilt R L γ δ
        ((MomentumTreeData.spectralLinksSpatial (P := P.withRootInput)) (spatialFrequencyLinks Q (G.base.frequency a))
          z ξ) φ I) 1 ≤ N) :
    Fourier.mixedFourierNorm θ J 0
      (fun t k => (MomentumTreeData.fourierRootPartitionSourceTreeExtensionFilt (P := P)) (G.at k) ζ R χ L γ δ Q φ I
        f S t k) ≤
      ENNReal.ofReal (rootJetConstant J) * (treeCellConstant d m J K M n C B * G.momentMass J) *
        Fourier.mixedFourierNorm00 θ
          (fun t (u : (SourceCellIndex S × (LocalizedCellIndex n (m + 1) → Fin d → ℝ)) × α) =>
            (MomentumTreeData.allCellTreeKernelSpatialFilt (P := P.withRootInput)) R χ L γ δ
              (spatialFrequencyLinks Q (G.base.frequency u.2)) φ I S t u.1) := by
  let U := SourceCellIndex S × (LocalizedCellIndex n (m + 1) → Fin d → ℝ)
  let Kt := fun t (u : U × α) => (MomentumTreeData.allCellTreeKernelSpatialFilt (P := P.withRootInput)) R χ L γ δ
    (spatialFrequencyLinks Q (G.base.frequency u.2)) φ I S t u.1
  let Cphys := Fourier.cutoffKernelL1Factor hc.radius hc.bound * Fourier.localTimeL1Factor 1 hc.radius hc.bound
  have hCphys : Cphys < ⊤ := ENNReal.mul_lt_top (Fourier.cutoffKernelL1Factor_ne_top _ _).lt_top
    (Fourier.localTimeL1Factor_ne_top (le_refl (1 : ℝ)) _ _).lt_top
  have hphys (u : U × α) : eLpNorm (fun t => Kt t u) 1 ≤ Cphys * N :=
    (eLpNorm_cutoffTriangleIntegral_one_le hχ hc
      (RootCoordinates.integrable_linkDensityFilt R hLp γ δ
        ((MomentumTreeData.spectralLinksSpatial (P := P.withRootInput)) (spatialFrequencyLinks Q (G.base.frequency u.2))
          u.1.1.2.val u.1.2) φ hI hbox)).trans (mul_le_mul' le_rfl (hroot u.1.1.2.val u.1.2 u.2))
  have hfull := mixedFourierNorm_rootProductRootMixture_le (N := J) (sourceCellMeasure S) G θ
    ((MomentumTreeData.treeRootSpectralAmplitudeSpatial (P := P)) ζ f S) (treeRootSpectralEnvelopeSpatial J f S)
    ((MomentumTreeData.treeRootSpectralAmplitude_eq_zeroSpatial (P := P)) ζ f S)
    (fun q u => ((MomentumTreeData.contDiff_treeRootSpectralAmplitudeSpatial (P := P)) ζ f S q u).of_le (by simp))
    (fun q j _ k => stronglyMeasurable_rootTreeJets P ζ f S G.root_measurable (by omega) hf q k j)
    (integrable_treeRootSpectralEnvelopeSpatial J f S hS hK hM hf)
    (measurable_treeRootSpectralEnvelopeSpatial J f S (by omega) hf)
    (treeRootSpectralEnvelope_nonnegSpatial J f S)
    (fun q j hj k u => (MomentumTreeData.norm_iteratedFDeriv_treeRootSpectralAmplitude_leSpatial (P := P)) ζ f S q
      hj k u)
    (lintegral_treeRootSpectralEnvelope_leSpatial J f S hS hK hM hB hf) Kt
    ((MomentumTreeData.stronglyMeasurable_treeSpatialFrequencyFilt (P := P.withRootInput)) G.base.frequency
      G.base.frequency_measurable hχ.continuous.measurable R hLp γ δ Q φ I hI S)
    (fun u => integrable_cutoffTriangleIntegral hχ hc
      (RootCoordinates.integrable_linkDensityFilt R hLp γ δ
        ((MomentumTreeData.spectralLinksSpatial (P := P.withRootInput)) (spatialFrequencyLinks Q (G.base.frequency u.2))
          u.1.1.2.val u.1.2) φ hI hbox))
    (ENNReal.mul_lt_top hCphys hN) hphys hfin
  change Fourier.mixedFourierNorm θ J 0
    (fun t k => ∫ u, (G.at k).amplitude u.2 * rootAmplitudeSumSpatial
      ((MomentumTreeData.treeRootSpectralAmplitudeSpatial (P := P)) ζ f S) k u.1 * Kt t u
        ∂(sourceCellMeasure S).prod G.base.μ) ≤ _
  apply hfull.trans_eq
  unfold treeCellConstant
  ring

end WaveTurbulence.Flower.FiltGate
