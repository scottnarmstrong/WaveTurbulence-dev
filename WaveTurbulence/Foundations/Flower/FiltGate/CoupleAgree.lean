/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltGate.CoupleExt
public import WaveTurbulence.Foundations.Flower.FiltSrc.Spectral
public import WaveTurbulence.Foundations.Flower.FiltSrc.Cells
public import WaveTurbulence.Foundations.Flower.FiltSrc.Source
public import WaveTurbulence.Foundations.Flower.FiltProd.Couple
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.WeightedCoupleAgreement
public import WaveTurbulence.Foundations.Flower.IncTop.Top.CoupleRootRestriction

/-! # D5b-3 FILT-GATE: agreement of the filtered couple extensions with the raw operators

Twins (copied by source from INC-TOP, sha256 in COPIED-SHA256SUMS; `φ` inserted after the links, the filter bound
`hφ : ∀ i u, ‖φ i u‖ ≤ Bφ` where the source identities need it):
- `Reg/MaskedCouplePointwise`: `integrable_allCellMaskedCoupleSlice_of_uniformRootL1SpatialFilt`,
  `allCellMaskedSourceCoupleExtension_eq_tsumSpatialFilt`;
- `Reg/MaskedRawCoupleUpperAgreement`: `allCellMaskedSourceCoupleExtension_agrees_aboveSpatialFilt`;
- `Reg/WeightedCoupleAgreement`: `fourierMaskedSourceCoupleExtension_agrees_aboveFilt`;
- `Top/CoupleRootRestriction`: `allCellMaskedSourceCoupleExtension_agrees_oneClock_aboveSpatialFilt`,
  `fourierMaskedSourceCoupleExtension_agrees_oneClockFilt`.

The scalar inputs are D5b-2's (`FiltProd.Couple`: `enorm_coupleExtension_leFilt`, `coupleExtension_agrees_aboveFilt`,
`cumulativeKernel_eq_oneClockKernelFilt`) and D5b-1's source identities (`FiltSrc.Cells`, `Spectral`, `Source`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.FiltGate
open WaveTurbulence.Incoh WaveTurbulence.Flower.IncTop WaveTurbulence.Flower.FiltSrc
  WaveTurbulence.Flower.FiltProd

/-- Conditional pointwise Fubini typing from the root-marginal bound (filtered). -/
theorem MomentumTreeData.integrable_allCellMaskedCoupleSlice_of_uniformRootL1SpatialFilt {d n m w K M : ℕ}
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
    (τ t : Fin 2 → ℝ) (k : Mom d) :
    Integrable (fun u => (MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S k u *
      (MomentumTreeData.allCellCutoffCoupleKernelSpatialFilt (P := P)) χ R L γ δ Q φ I S (t + τ) u)
      (sourceCellMeasure S) := by
  have hKs : StronglyMeasurable
      ((MomentumTreeData.allCellCutoffCoupleKernelSpatialFilt (P := P)) χ R L γ δ Q φ I S (t + τ)) :=
    ((MomentumTreeData.stronglyMeasurable_allCellCutoffCoupleKernelSpatialFilt (P := P)) hχ.continuous.measurable
      R hL γ δ Q φ I hI S).comp_measurable
      (g := fun u => (t + τ, u)) (measurable_const.prodMk measurable_id)
  apply integrable_mul_of_uniform_enorm_bound (sourceCellMeasure S)
    ((MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S k)
    ((MomentumTreeData.allCellCutoffCoupleKernelSpatialFilt (P := P)) χ R L γ δ Q φ I S (t + τ))
    ((MomentumTreeData.integrable_allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S hS hK hM hB h k)
    hKs.aestronglyMeasurable
    (N := ENNReal.ofReal hc.bound ^ 4 * N) (ENNReal.mul_lt_top (by finiteness) hN)
  intro u
  exact (RootCoordinates.enorm_coupleExtension_leFilt R hχ hc hL γ δ
    ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.1.2.val u.2) φ hI hbox (t + τ)).trans
      (mul_le_mul' le_rfl (hb _ _))

/-- The filtered masked extension is the sum of its cell spectral integrals at every external time. -/
theorem MomentumTreeData.allCellMaskedSourceCoupleExtension_eq_tsumSpatialFilt {d n m w K M : ℕ}
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
    (τ t : Fin 2 → ℝ) (k : Mom d) :
    (MomentumTreeData.allCellMaskedSourceCoupleExtensionSpatialFilt (P := P)) χ ζ R L γ δ Q φ I f S τ t k =
      ∑' u : SourceCellIndex S, ∫ ξ : LocalizedCellIndex n m → Fin d → ℝ,
        (MomentumTreeData.maskedSourceSpectralAmplitudeSpatial (P := P)) ζ f u.1 u.2.val k ξ *
          RootCoordinates.coupleExtensionFilt R χ L γ δ
            ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.2.val ξ) φ I (t + τ) := by
  have hs := (MomentumTreeData.integrable_allCellMaskedCoupleSlice_of_uniformRootL1SpatialFilt (P := P))
    hχ hc ζ R L γ δ Q φ I hI hbox f S hS hL hK hM hB h hN hb τ t k
  change Integrable (fun u => (MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S k u *
    (MomentumTreeData.allCellCutoffCoupleKernelSpatialFilt (P := P)) χ R L γ δ Q φ I S (t + τ) u)
      (Measure.count.prod volume) at hs
  change (∫ u, (MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S k u *
    (MomentumTreeData.allCellCutoffCoupleKernelSpatialFilt (P := P)) χ R L γ δ Q φ I S (t + τ) u
      ∂(Measure.count.prod volume)) = _
  rw [integral_prod _ hs, integral_countable hs.integral_prod_left]
  simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
  rfl

/-- The filtered masked extension agrees with the unlocalized filtered source on the whole root box. -/
theorem MomentumTreeData.allCellMaskedSourceCoupleExtension_agrees_aboveSpatialFilt {d n m w K M : ℕ}
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
    (t : Fin 2 → ℝ) (ht : R.baseRootTimes Q ≤ t)
    (hχone : ∀ j : Fin 2, ∀ s ∈ Set.Icc (0 : ℝ) ((t - R.baseRootTimes Q) j), χ s = 1) (k : Mom d) :
    (MomentumTreeData.allCellMaskedSourceCoupleExtensionSpatialFilt (P := P)) χ ζ R L γ δ Q φ I f S 0 t k =
      (MomentumTreeData.sourceCoupleKernelSpatialFilt (P := P)) ζ R L γ δ Q φ I f t k := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  rw [(MomentumTreeData.allCellMaskedSourceCoupleExtension_eq_tsumSpatialFilt (P := P)) hχ hc ζ R L γ δ Q φ I
    hI hbox f S hS hLp hK hM hB h hN hb]
  unfold MomentumTreeData.sourceCoupleKernelSpatialFilt
  rw [(MomentumTreeData.sourceIntegral_eq_tsum_localizedSourceIntegralSpatialFilt (P := P)) ζ L γ δ Q φ hφ
    (I ∩ R.rootCut t) (Set.inter_subset_left.trans hbox) f S hcover hS hL hK hM hB h k]
  apply tsum_congr
  intro u
  rw [← (RootInputCoordinates.sourceRootMask_mul_localizedSourceIntegralSpatialFilt (C := Croot)) ζ L γ δ Q φ
    (I ∩ R.rootCut t) f u.1 u.2.val k]
  rw [(MomentumTreeData.localizedSourceIntegral_eq_linkKernelMixtureSpatialFilt (P := P)) ζ L γ δ Q φ
    (I ∩ R.rootCut t) (Set.inter_subset_left.trans hbox) f u.1 u.2.val hLp hK hB h k]
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro ξ
  dsimp only
  simp only [add_zero, MomentumTreeData.maskedSourceSpectralAmplitudeSpatial]
  have hbase : R.baseRootTimes ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.2.val ξ) =
      R.baseRootTimes Q := rfl
  rw [RootCoordinates.coupleExtension_agrees_aboveFilt R hLp γ δ
    ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.2.val ξ) φ hI hbox t
    (hbase ▸ ht) (by simpa only [hbase] using hχone)]
  simp only [RootCoordinates.cumulativeKernelFilt, mul_assoc]

/-- Pointwise agreement of the common filtered Fourier extension and the weighted raw couple. -/
theorem MomentumTreeData.fourierMaskedSourceCoupleExtension_agrees_aboveFilt
    {d n m w K M : ℕ} {α : Type} [MeasurableSpace α]
    (P : MomentumTreeData n m w) (F : Cut2A.SpatialMeasure (PairedMomentum d n) α)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : Fourier.CutoffControl χ)
    (Croot : RootInputCoordinates P) (ζ : Circle) (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    {Bφ : ℝ} (hφ : ∀ i u, ‖φ i u‖ ≤ Bφ) (I : Set (Fin n → Fin 2 → ℝ))
    (hI : MeasurableSet I) (hbox : I ⊆ univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, P.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin n × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    {C B : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n)
    (hL : 1 ≤ L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    {N : ℝ≥0∞} (hN : N < ⊤)
    (hroot : ∀ z ξ a, eLpNorm (RootCoordinates.linkDensityFilt R L γ δ
      ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (F.frequency a)) z ξ) φ I) 1 ≤ N)
    (t : Fin 2 → ℝ) (ht : R.baseRootTimes Q ≤ t)
    (hχone : ∀ j : Fin 2, ∀ s ∈ Icc (0 : ℝ) ((t - R.baseRootTimes Q) j), χ s = 1) (k : Mom d) :
    (MomentumTreeData.fourierMaskedSourceCoupleExtensionFilt (P := P)) F χ ζ R L γ δ Q φ I f S 0 t k =
      (MomentumTreeData.weightedSourceCoupleKernelFilt (P := P)) F ζ R L γ δ Q φ I f t k := by
  have hLp := zero_lt_one.trans_le hL
  let A := (MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S k
  let G := fun u : (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) × α =>
    (MomentumTreeData.allCellCutoffCoupleKernelSpatialFilt (P := P)) χ R L γ δ
      (spatialFrequencyLinks Q (F.frequency u.2)) φ I S t u.1
  have hmG := ((MomentumTreeData.stronglyMeasurable_coupleSpatialFrequencyFilt (P := P)) F.frequency
    F.frequency_measurable hχ.continuous.measurable R hLp γ δ Q φ I hI S).comp_measurable
      (g := fun u => (t, u)) (measurable_const.prodMk measurable_id)
  have hiA := (MomentumTreeData.integrable_allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S hS hK hM hB hf k
  have hb (u : (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) × α) :
      ‖G u‖ₑ ≤ ENNReal.ofReal hc.bound ^ 4 * N :=
    (RootCoordinates.enorm_coupleExtension_leFilt R hχ hc hLp γ δ
      ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (F.frequency u.2))
        u.1.1.2.val u.1.2) φ hI hbox t).trans
      (mul_le_mul' le_rfl (hroot u.1.1.2.val u.1.2 u.2))
  have he := integral_product_amplitude_kernel (sourceCellMeasure S) F A hiA G hmG.aestronglyMeasurable
    (ENNReal.mul_lt_top (by finiteness) hN) hb
  rw [(MomentumTreeData.weightedSourceCoupleKernelFilt_eq_integral_of_summable (P := P)) F ζ R L γ δ Q φ hφ I
    hbox f k ((MomentumTreeData.summable_norm_sourceLeafWeight_latticeSpatial (P := P)) f S hcover hS hL hK hM
      hB hf k)]
  unfold MomentumTreeData.fourierMaskedSourceCoupleExtensionFilt
  simp only [add_zero]
  rw [he]
  apply integral_congr_ae
  apply ae_of_all
  intro a
  dsimp only
  apply congrArg (fun z : ℂ => F.amplitude a * z)
  simpa only [MomentumTreeData.allCellMaskedSourceCoupleExtensionSpatialFilt, add_zero] using
    (MomentumTreeData.allCellMaskedSourceCoupleExtension_agrees_aboveSpatialFilt (P := P)) hχ hc Croot ζ R L γ δ
    (spatialFrequencyLinks Q (F.frequency a)) φ hφ I hI hbox f S hcover hS hL hK hM hB hf
    hN (fun z ξ => hroot z ξ a) t ht hχone k

/-- The one-clock cut (main's `cumulativeKernel_eq_oneClockKernel`, set form): above the passive root layer only the
active clock constrains the source. (D5b-2's `oneClockKernelFilt` has no exposed body, so the set identity is used.) -/
theorem inter_rootCut_eq_oneClockCut {d n : ℕ} (R : RootCoordinates n) (a : Fin 2)
    (Q : Fin n → LayerLink d) {I : Set (Fin n → Fin 2 → ℝ)}
    (hbox : I ⊆ univ.pi (fun i => linkBox (Q i))) {t : Fin 2 → ℝ}
    (ht : ∀ j, j ≠ a → R.baseRootTimes Q j + 1 ≤ t j) :
    I ∩ R.rootCut t = I ∩ R.oneClockCut a (t a) := by
  ext w
  constructor
  · rintro ⟨hi, hc⟩
    exact ⟨hi, hc.1 a⟩
  · rintro ⟨hi, hc⟩
    refine ⟨hi, ?_⟩
    have hb : (R.equiv w).1 ∈ R.rootBox Q := by
      apply ((R.equiv_symm_mem_linkBoxes Q (R.equiv w).1 (R.equiv w).2).mp ?_).1
      simpa only [Prod.eta, MeasurableEquiv.symm_apply_apply] using hbox hi
    change (R.equiv w).1 ≤ t ∧ (R.equiv w).2 ∈ univ
    refine ⟨fun j => ?_, mem_univ _⟩
    by_cases hj : j = a
    · subst j
      exact hc
    · exact (hb.2 j).trans (ht j hj)

/-- The filtered one-clock masked recovery (twin of `allCellMaskedSourceCoupleExtension_agrees_oneClock_aboveSpatial`). -/
theorem allCellMaskedSourceCoupleExtension_agrees_oneClock_aboveSpatialFilt
    {d n m w K M : ℕ} (P : MomentumTreeData n m w) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : Fourier.CutoffControl χ) (Croot : RootInputCoordinates P) (ζ : Circle)
    (R : RootCoordinates n) (a : Fin 2) (b : ℝ)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
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
    (t : Fin 2 → ℝ)
    (ht : R.baseRootTimes Q ≤ t + R.oneClockShift a Q b)
    (hpass : ∀ j, j ≠ a → R.baseRootTimes Q j + 1 ≤ (t + R.oneClockShift a Q b) j)
    (hχone : ∀ j : Fin 2, ∀ s ∈ Set.Icc (0 : ℝ)
      ((t + R.oneClockShift a Q b - R.baseRootTimes Q) j), χ s = 1) (k : Mom d) :
    (MomentumTreeData.allCellMaskedSourceCoupleExtensionSpatialFilt (P := P)) χ ζ R L γ δ Q φ I f S
      (R.oneClockShift a Q b) t k = sourceOneClockKernelSpatialFilt P ζ R a L γ δ Q φ I f t k := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  rw [(MomentumTreeData.allCellMaskedSourceCoupleExtension_eq_tsumSpatialFilt (P := P)) hχ hc ζ R L γ δ Q φ I
    hI hbox f S hS hLp hK hM hB h hN hb]
  unfold sourceOneClockKernelSpatialFilt
  rw [(MomentumTreeData.sourceIntegral_eq_tsum_localizedSourceIntegralSpatialFilt (P := P)) ζ L γ δ Q φ hφ
    (I ∩ R.oneClockCut a (t a)) (Set.inter_subset_left.trans hbox) f S hcover hS hL hK hM hB h k]
  apply tsum_congr
  intro u
  calc
    _ = sourceRootMask u.1 k * (MomentumTreeData.localizedSourceIntegralSpatialFilt (P := P)) ζ L γ δ Q φ
        (I ∩ R.oneClockCut a (t a)) f u.1 u.2.val k := by
      rw [(MomentumTreeData.localizedSourceIntegral_eq_linkKernelMixtureSpatialFilt (P := P)) ζ L γ δ Q φ
        (I ∩ R.oneClockCut a (t a)) (Set.inter_subset_left.trans hbox) f u.1 u.2.val hLp hK hB h k,
        ← integral_const_mul]
      apply integral_congr_ae
      apply ae_of_all
      intro ξ
      dsimp only
      have hbase : R.baseRootTimes ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.2.val ξ) =
          R.baseRootTimes Q := rfl
      have hshift : R.oneClockShift a ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.2.val ξ) b =
          R.oneClockShift a Q b := rfl
      have he := RootCoordinates.coupleExtension_agrees_aboveFilt R hLp γ δ
        ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.2.val ξ) φ
        hI hbox (t + R.oneClockShift a Q b) (hbase ▸ ht) (by simpa only [hbase] using hχone)
      change RootCoordinates.coupleExtensionFilt R χ L γ δ
        ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.2.val ξ) φ I
        (t + R.oneClockShift a Q b) = _ at he
      rw [he, RootCoordinates.cumulativeKernelFilt, inter_rootCut_eq_oneClockCut R a
        ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.2.val ξ) hbox
        (by simpa only [hbase] using hpass)]
      simp only [Pi.add_apply, RootCoordinates.oneClockShift, ite_true, add_zero]
      unfold MomentumTreeData.maskedSourceSpectralAmplitudeSpatial
      ring
    _ = _ := (RootInputCoordinates.sourceRootMask_mul_localizedSourceIntegralSpatialFilt (C := Croot)) ζ L γ δ Q φ
      (I ∩ R.oneClockCut a (t a)) f u.1 u.2.val k

/-- Weighted one-clock agreement of the translated common filtered Fourier extension (any measure `F`). -/
theorem fourierMaskedSourceCoupleExtension_agrees_oneClockFilt
    {d n m w K M : ℕ} {α : Type} [MeasurableSpace α]
    (P : MomentumTreeData n m w) (F : Cut2A.SpatialMeasure (PairedMomentum d n) α)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : Fourier.CutoffControl χ)
    (Croot : RootInputCoordinates P) (ζ : Circle) (R : RootCoordinates n) (a : Fin 2) (b : ℝ)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    {Bφ : ℝ} (hφ : ∀ i u, ‖φ i u‖ ≤ Bφ) (I : Set (Fin n → Fin 2 → ℝ))
    (hI : MeasurableSet I) (hbox : I ⊆ univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, P.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin n × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    {C B : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n)
    (hL : 1 ≤ L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    {N : ℝ≥0∞} (hN : N < ⊤)
    (hroot : ∀ z ξ a, eLpNorm (RootCoordinates.linkDensityFilt R L γ δ
      ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (F.frequency a)) z ξ) φ I) 1 ≤ N)
    (t : Fin 2 → ℝ)
    (ht : R.baseRootTimes Q ≤ t + R.oneClockShift a Q b)
    (hpass : ∀ j, j ≠ a → R.baseRootTimes Q j + 1 ≤ (t + R.oneClockShift a Q b) j)
    (hχone : ∀ j : Fin 2, ∀ s ∈ Set.Icc (0 : ℝ)
      ((t + R.oneClockShift a Q b - R.baseRootTimes Q) j), χ s = 1) (k : Mom d) :
    (MomentumTreeData.fourierMaskedSourceCoupleExtensionFilt (P := P)) F χ ζ R L γ δ Q φ I f S
        (R.oneClockShift a Q b) t k =
      weightedSourceOneClockKernelFilt P F ζ R a L γ δ Q φ I f t k := by
  have hLp := zero_lt_one.trans_le hL
  let A := (MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S k
  let G := fun u : (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) × α =>
    (MomentumTreeData.allCellCutoffCoupleKernelSpatialFilt (P := P)) χ R L γ δ
      (spatialFrequencyLinks Q (F.frequency u.2)) φ I S (t + R.oneClockShift a Q b) u.1
  have hmG := ((MomentumTreeData.stronglyMeasurable_coupleSpatialFrequencyFilt (P := P)) F.frequency
    F.frequency_measurable hχ.continuous.measurable R hLp γ δ Q φ I hI S).comp_measurable
      (g := fun u => (t + R.oneClockShift a Q b, u)) (measurable_const.prodMk measurable_id)
  have hiA := (MomentumTreeData.integrable_allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S hS hK hM hB hf k
  have hb (u : (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) × α) :
      ‖G u‖ₑ ≤ ENNReal.ofReal hc.bound ^ 4 * N :=
    (RootCoordinates.enorm_coupleExtension_leFilt R hχ hc hLp γ δ
      ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (F.frequency u.2))
        u.1.1.2.val u.1.2) φ hI hbox (t + R.oneClockShift a Q b)).trans
      (mul_le_mul' le_rfl (hroot u.1.1.2.val u.1.2 u.2))
  have he := integral_product_amplitude_kernel (sourceCellMeasure S) F A hiA G hmG.aestronglyMeasurable
    (ENNReal.mul_lt_top (by finiteness) hN) hb
  have hsum := (MomentumTreeData.summable_norm_sourceLeafWeight_latticeSpatial (P := P)) f S hcover hS hL hK hM
    hB hf k
  unfold weightedSourceOneClockKernelFilt
  rw [(MomentumTreeData.weightedSourceIntegralFilt_eq_integral_of_summable (P := P)) F ζ L γ δ Q φ hφ
    (I ∩ R.oneClockCut a (t a)) (inter_subset_left.trans hbox) f k hsum]
  unfold MomentumTreeData.fourierMaskedSourceCoupleExtensionFilt
  rw [he]
  apply integral_congr_ae
  apply ae_of_all
  intro a'
  dsimp only
  apply congrArg (fun z : ℂ => F.amplitude a' * z)
  have hbox' : I ⊆ univ.pi (fun i => linkBox (spatialFrequencyLinks Q (F.frequency a') i)) := hbox
  exact allCellMaskedSourceCoupleExtension_agrees_oneClock_aboveSpatialFilt P hχ hc Croot ζ R a b L γ δ
    (spatialFrequencyLinks Q (F.frequency a')) φ hφ I hI hbox' f S hcover hS hL hK hM hB hf
    hN (fun z ξ => hroot z ξ a') t ht hpass hχone k

end WaveTurbulence.Flower.FiltGate
