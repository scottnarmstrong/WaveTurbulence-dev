/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltSrc.Spectral
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.FrequencyTranslation
public import WaveTurbulence.Foundations.Incoh.ParametricDoubleIntegral
public import WaveTurbulence.Foundations.Incoh.ParametricTriangleIntegral

/-! # D5b-1 FILT-SRC: joint measurability of the filtered spectral families (D5B-MAP K5, K3)

Twins (multiplier `φ` after the links; objects of `Density.lean`) of INC-TOP's
- `Reg/SpectralRootMeasurability`: `measurable_spectral_normalizedLinkIntegrandSpatial`,
  `stronglyMeasurable_spectral_linkDensitySpatial`;
- `Reg/SpectralCoupleMeasurability`: `stronglyMeasurable_spectral_localLinkDensitySpatial`,
  `stronglyMeasurable_spectral_coupleExtensionSpatial`;
- `Reg/SpectralTreeMeasurability`: `stronglyMeasurable_spectral_treeExtensionSpatial`;
- `Reg/AllCellCutoffCoupleFamily`, `Reg/AllCellTreeFamily`: the all-cell kernel families and their measurability
  (needed by the next item; D5b-3 imports them);
- `Reg/FrequencyTranslation`: `stronglyMeasurable_coupleSpatialFrequency`, `stronglyMeasurable_treeSpatialFrequency`
  (K3: the character frequency translates the spectral variable only; `φ` is attached to the link index).

Copied by source (sha256 in COPIED-SHA256SUMS). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Flower.FiltSrc
open WaveTurbulence.Incoh WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.IncTop

/-! ### `Reg/SpectralRootMeasurability` -/

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The filtered normalized spectral link integrand is jointly measurable. -/
theorem MomentumTreeData.measurable_spectral_normalizedLinkIntegrandSpatialFilt {d n m w : ℕ}
    (P : MomentumTreeData n m w) {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I) :
    Measurable (fun v : (Fin n → Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ) =>
      normalizedLinkIntegrandFilt L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z v.2) φ I v.1) := by
  have hp : Continuous (fun v : (Fin n → Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ) =>
      ∏ i, filtLinkTimeFactor L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z v.2 i) (φ i) (v.1 i)) := by
    apply continuous_finsetProd
    intro i _
    exact ((MomentumTreeData.continuous_spectral_linkTimeFactorSpatialFilt (P := P)) hL γ δ Q φ z i).comp
      (f := fun v : (Fin n → Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ) => (v.1 i, v.2))
      (by fun_prop)
  convert (hp.measurable.indicator (hI.preimage measurable_fst)).const_mul
    (((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) : ℝ) : ℂ) using 1
  funext v
  by_cases hv : v.1 ∈ I <;> simp [normalizedLinkIntegrandFilt, hv]

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Filtered spectral root marginals form a jointly strongly measurable family. -/
theorem MomentumTreeData.stronglyMeasurable_spectral_linkDensitySpatialFilt {d n m w r : ℕ}
    (P : MomentumTreeData n m w) (R : RootCoordinates n r) {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I) :
    StronglyMeasurable (fun v : (Fin r → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ) =>
      RootCoordinates.linkDensityFilt R L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z v.2) φ I v.1) := by
  have he : Measurable (fun v : ((Fin r → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ)) ×
      (Fin R.restCount → ℝ) => R.equiv.symm (v.1.1, v.2)) :=
    R.equiv.symm.measurable.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hn := ((MomentumTreeData.measurable_spectral_normalizedLinkIntegrandSpatialFilt (P := P))
    hL γ δ Q φ z hI).stronglyMeasurable
  exact (hn.comp_measurable (he.prodMk (measurable_snd.comp measurable_fst))).integral_prod_right'

/-! ### `Reg/SpectralCoupleMeasurability` -/

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Filtered local spectral root densities form a jointly strongly measurable family. -/
theorem MomentumTreeData.stronglyMeasurable_spectral_localLinkDensitySpatialFilt {d n m w : ℕ}
    (P : MomentumTreeData n m w) (R : RootCoordinates n) {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I) :
    StronglyMeasurable (fun v : (Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ) =>
      RootCoordinates.localLinkDensityFilt R L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z v.2)
        φ I v.1) := by
  have h := (MomentumTreeData.stronglyMeasurable_spectral_linkDensitySpatialFilt (P := P)) R hL γ δ Q φ z hI
  exact h.comp_measurable
    (g := fun v : (Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ) =>
      (v.1 + R.baseRootTimes Q, v.2)) (by fun_prop)

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The filtered spectral couple extensions satisfy the joint measurability needed by Tonelli. -/
theorem MomentumTreeData.stronglyMeasurable_spectral_coupleExtensionSpatialFilt {d n m w : ℕ}
    (P : MomentumTreeData n m w) (R : RootCoordinates n) {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I) {χ : ℝ → ℝ} (hχ : Measurable χ) :
    StronglyMeasurable (fun v : (Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ) =>
      RootCoordinates.coupleExtensionFilt R χ L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z v.2)
        φ I v.1) := by
  have h := stronglyMeasurable_cutoffDoubleIntegral_family hχ
    (fun v : (Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ) =>
      RootCoordinates.localLinkDensityFilt R L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z v.2)
        φ I v.1)
    ((MomentumTreeData.stronglyMeasurable_spectral_localLinkDensitySpatialFilt (P := P)) R hL γ δ Q φ z hI)
  exact h.comp_measurable
    (g := fun v : (Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ) =>
      (v.1 - R.baseRootTimes Q, v.2)) (by fun_prop)

/-! ### `Reg/SpectralTreeMeasurability` -/

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Filtered causal spectral tree extensions form a jointly strongly measurable family. -/
theorem MomentumTreeData.stronglyMeasurable_spectral_treeExtensionSpatialFilt {d n m w : ℕ}
    (P : MomentumTreeData n m w) (R : RootCoordinates n) {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I) {χ : ℝ → ℝ} (hχ : Measurable χ) :
    StronglyMeasurable (fun v : (Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ) =>
      Fourier.cutoffTriangleIntegral χ (RootCoordinates.linkDensityFilt R L γ δ
        ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z v.2) φ I) v.1) :=
  stronglyMeasurable_cutoffTriangleIntegral_family hχ
    (fun v : (Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ) =>
      RootCoordinates.linkDensityFilt R L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z v.2) φ I v.1)
    ((MomentumTreeData.stronglyMeasurable_spectral_linkDensitySpatialFilt (P := P)) R hL γ δ Q φ z hI)

/-! ### `Reg/AllCellCutoffCoupleFamily`, `Reg/AllCellTreeFamily` -/

/-- The filtered scalar link extension over every selected localization cell (couples). -/
def MomentumTreeData.allCellCutoffCoupleKernelSpatialFilt {d n m w : ℕ}
    (P : MomentumTreeData n m w) (χ : ℝ → ℝ) (R : RootCoordinates n) (L γ δ : ℝ)
    (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (I : Set (Fin n → Fin 2 → ℝ))
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (t : Fin 2 → ℝ) (u : SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) : ℂ :=
  RootCoordinates.coupleExtensionFilt R χ L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.1.2.val u.2)
    φ I t

/-- Joint clock/spectral measurability of the full countable filtered couple kernel family. -/
theorem MomentumTreeData.stronglyMeasurable_allCellCutoffCoupleKernelSpatialFilt {d n m w : ℕ}
    (P : MomentumTreeData n m w) {χ : ℝ → ℝ} (hχ : Measurable χ) (R : RootCoordinates n) {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (I : Set (Fin n → Fin 2 → ℝ))
    (hI : MeasurableSet I) (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ)) :
    StronglyMeasurable (fun v : (Fin 2 → ℝ) ×
      (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) =>
        (MomentumTreeData.allCellCutoffCoupleKernelSpatialFilt (P := P)) χ R L γ δ Q φ I S v.1 v.2) := by
  have hm : Measurable (fun v : SourceCellIndex S ×
      ((Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ)) =>
      RootCoordinates.coupleExtensionFilt R χ L γ δ
        ((MomentumTreeData.spectralLinksSpatial (P := P)) Q v.1.2.val v.2.2) φ I v.2.1) := by
    apply measurable_from_prod_countable_right
    intro u
    exact ((MomentumTreeData.stronglyMeasurable_spectral_coupleExtensionSpatialFilt (P := P))
      R hL γ δ Q φ u.2.val hI hχ).measurable
  have hg : Measurable (fun v : (Fin 2 → ℝ) ×
      (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) =>
        (v.2.1, (v.1, v.2.2))) := by fun_prop
  exact (hm.comp hg).stronglyMeasurable

/-- The filtered scalar link extension over every selected localization cell (trees). -/
def MomentumTreeData.allCellTreeKernelSpatialFilt {d n m w : ℕ}
    (P : MomentumTreeData n m w) (R : RootCoordinates n) (χ : ℝ → ℝ) (L γ δ : ℝ)
    (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (I : Set (Fin n → Fin 2 → ℝ))
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (t : Fin 2 → ℝ) (u : SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) : ℂ :=
  Fourier.cutoffTriangleIntegral χ (RootCoordinates.linkDensityFilt R L γ δ
    ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.1.2.val u.2) φ I) t

/-- Joint clock/spectral measurability of the full countable filtered tree kernel family. -/
theorem MomentumTreeData.stronglyMeasurable_allCellTreeKernelSpatialFilt {d n m w : ℕ}
    (P : MomentumTreeData n m w) (R : RootCoordinates n) {χ : ℝ → ℝ} (hχ : Measurable χ) {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (I : Set (Fin n → Fin 2 → ℝ))
    (hI : MeasurableSet I) (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ)) :
    StronglyMeasurable (fun v : (Fin 2 → ℝ) ×
      (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) =>
        (MomentumTreeData.allCellTreeKernelSpatialFilt (P := P)) R χ L γ δ Q φ I S v.1 v.2) := by
  have hm : Measurable (fun v : SourceCellIndex S ×
      ((Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ)) =>
      Fourier.cutoffTriangleIntegral χ (RootCoordinates.linkDensityFilt R L γ δ
        ((MomentumTreeData.spectralLinksSpatial (P := P)) Q v.1.2.val v.2.2) φ I) v.2.1) := by
    apply measurable_from_prod_countable_right
    intro u
    exact ((MomentumTreeData.stronglyMeasurable_spectral_treeExtensionSpatialFilt (P := P))
      R hL γ δ Q φ u.2.val hI hχ).measurable
  have hg : Measurable (fun v : (Fin 2 → ℝ) ×
      (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) =>
        (v.2.1, (v.1, v.2.2))) := by fun_prop
  exact (hm.comp hg).stronglyMeasurable

/-! ### `Reg/FrequencyTranslation` -/

/-- Joint measurability of the filtered couple family in clocks, localization variables and a measurable
character. -/
theorem MomentumTreeData.stronglyMeasurable_coupleSpatialFrequencyFilt {d n m w : ℕ}
    {α : Type*} [MeasurableSpace α] (P : MomentumTreeData n m w)
    (ν : α → PairedMomentum d n) (hν : Measurable ν)
    {χ : ℝ → ℝ} (hχ : Measurable χ) (R : RootCoordinates n) {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (I : Set (Fin n → Fin 2 → ℝ))
    (hI : MeasurableSet I) (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ)) :
    StronglyMeasurable (fun v : (Fin 2 → ℝ) ×
      ((SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) × α) =>
        (MomentumTreeData.allCellCutoffCoupleKernelSpatialFilt (P := P)) χ R L γ δ
          (spatialFrequencyLinks Q (ν v.2.2)) φ I S v.1 v.2.1) := by
  have he (t : Fin 2 → ℝ) (u : SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) (a : α) :
      (MomentumTreeData.allCellCutoffCoupleKernelSpatialFilt (P := P)) χ R L γ δ
          (spatialFrequencyLinks Q (ν a)) φ I S t u =
        (MomentumTreeData.allCellCutoffCoupleKernelSpatialFilt (P := P)) χ R L γ δ
          (spatialFrequencyLinks Q 0) φ I S t (u.1, u.2 + internalFrequency (ν a)) := by
    unfold MomentumTreeData.allCellCutoffCoupleKernelSpatialFilt
    rw [(MomentumTreeData.spectralLinksSpatial_frequency (P := P))]
  simp_rw [he]
  exact ((MomentumTreeData.stronglyMeasurable_allCellCutoffCoupleKernelSpatialFilt (P := P)) hχ R hL γ δ
    (spatialFrequencyLinks Q 0) φ I hI S).comp_measurable
      (g := fun v : (Fin 2 → ℝ) ×
        ((SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) × α) =>
        (v.1, (v.2.1.1, v.2.1.2 + internalFrequency (ν v.2.2))))
      (measurable_fst.prodMk
        (((measurable_fst.comp measurable_fst).comp measurable_snd).prodMk
          (((measurable_snd.comp measurable_fst).comp measurable_snd).add
            ((continuous_internalFrequency (d := d) (n := n) (m := m)).measurable.comp
              (hν.comp (measurable_snd.comp measurable_snd))))))

/-- Joint measurability of the filtered tree family in clocks, localization variables and a measurable
character. -/
theorem MomentumTreeData.stronglyMeasurable_treeSpatialFrequencyFilt {d n m w : ℕ}
    {α : Type*} [MeasurableSpace α] (P : MomentumTreeData n m w)
    (ν : α → PairedMomentum d n) (hν : Measurable ν)
    {χ : ℝ → ℝ} (hχ : Measurable χ) (R : RootCoordinates n) {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (I : Set (Fin n → Fin 2 → ℝ))
    (hI : MeasurableSet I) (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ)) :
    StronglyMeasurable (fun v : (Fin 2 → ℝ) ×
      ((SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) × α) =>
        (MomentumTreeData.allCellTreeKernelSpatialFilt (P := P)) R χ L γ δ
          (spatialFrequencyLinks Q (ν v.2.2)) φ I S v.1 v.2.1) := by
  have he (t : Fin 2 → ℝ) (u : SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) (a : α) :
      (MomentumTreeData.allCellTreeKernelSpatialFilt (P := P)) R χ L γ δ
          (spatialFrequencyLinks Q (ν a)) φ I S t u =
        (MomentumTreeData.allCellTreeKernelSpatialFilt (P := P)) R χ L γ δ
          (spatialFrequencyLinks Q 0) φ I S t (u.1, u.2 + internalFrequency (ν a)) := by
    unfold MomentumTreeData.allCellTreeKernelSpatialFilt
    rw [(MomentumTreeData.spectralLinksSpatial_frequency (P := P))]
  simp_rw [he]
  exact ((MomentumTreeData.stronglyMeasurable_allCellTreeKernelSpatialFilt (P := P)) R hχ hL γ δ
    (spatialFrequencyLinks Q 0) φ I hI S).comp_measurable
      (g := fun v : (Fin 2 → ℝ) ×
        ((SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) × α) =>
        (v.1, (v.2.1.1, v.2.1.2 + internalFrequency (ν v.2.2))))
      (measurable_fst.prodMk
        (((measurable_fst.comp measurable_fst).comp measurable_snd).prodMk
          (((measurable_snd.comp measurable_fst).comp measurable_snd).add
            ((continuous_internalFrequency (d := d) (n := n) (m := m)).measurable.comp
              (hν.comp (measurable_snd.comp measurable_snd))))))

end WaveTurbulence.Flower.FiltSrc
