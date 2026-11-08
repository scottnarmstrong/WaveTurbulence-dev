/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.RawModulation
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.AllCellCutoffCoupleFamily
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.AllCellTreeFamily

/-! Ported by source from C2-B-TOP `Cut2BReg.FrequencyTranslation` (sha256 in COPIED-SHA256SUMS); mechanical edits only.
 # Internal characters translate only the half-cell spectral variables

This identity supplies joint character measurability without placing any
regularity requirement on the Fourier measure's integrable amplitude.
-/

public section
noncomputable section
open MeasureTheory WithLp

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
/-- Embed a spatial character in the half-cell Fourier coordinates, leaving inputs unchanged. -/
@[expose] def internalFrequency {d n m : ℕ} (ν : PairedMomentum d n) :
    LocalizedCellIndex n m → Fin d → ℝ
  | .inl _ => 0
  | .inr p => (ν p).ofLp

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The transpose momentum map is additive. -/
theorem MomentumTreeData.spectralShift_add {d n m w : ℕ} (P : MomentumTreeData n m w)
    (ξ υ : LocalizedCellIndex n m → Fin d → ℝ) (j : MomentumCoordinate n) :
    P.spectralShift (ξ + υ) j = P.spectralShift ξ j + P.spectralShift υ j := by
  simp only [spectralShift, Pi.add_apply, toLp_add, smul_add, Finset.sum_add_distrib]

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The embedded character has the original frequency at every internal paired coordinate. -/
theorem MomentumTreeData.spectralShift_internalFrequency {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ν : PairedMomentum d n) (p : Fin n × Fin 2) :
    P.spectralShift (internalFrequency (m := m) ν) (some p) = ν p := by
  classical
  simp [spectralShift, internalFrequency, profileRow, Fintype.sum_sum_type,
    momentumUnitRow]

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Literal link parameters at arbitrary character frequency are a translated fixed family. -/
theorem MomentumTreeData.spectralLinksSpatial_frequency {d n m w : ℕ}
    (P : MomentumTreeData n m w) (Q : Fin n → LayerLink d) (ν : PairedMomentum d n)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (ξ : LocalizedCellIndex n m → Fin d → ℝ) :
    (MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q ν) z ξ =
      (MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q 0) z (ξ + internalFrequency ν) := by
  funext i
  simp only [spectralLinksSpatial, spatialFrequencyLinks, (MomentumTreeData.spectralShift_add (P := P)),
    (MomentumTreeData.spectralShift_internalFrequency (P := P)), PiLp.zero_apply, add_zero]

/-- The translation is jointly continuous. -/
theorem continuous_internalFrequency {d n m : ℕ} :
    Continuous (internalFrequency (d := d) (n := n) (m := m)) := by
  apply continuous_pi
  intro i
  cases i with
  | inl a => exact continuous_const
  | inr p => dsimp only [internalFrequency]; fun_prop

open WaveTurbulence.Incoh.TreeClockFibers in
/-- Spatial characters preserve every structural clock fiber and its literal domain. -/
@[expose] def TreeClockFibers.spatialFrequency {d n l : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers l Q) (ν : PairedMomentum d n) : TreeClockFibers l (spatialFrequencyLinks Q ν) where
  selection := T.selection
  remainingDomain := T.remainingDomain
  measurable_remainingDomain := T.measurable_remainingDomain
  lower := T.lower
  upper := T.upper
  measurable_lower := T.measurable_lower
  measurable_upper := T.measurable_upper
  lower_le_upper := T.lower_le_upper
  remaining_mem_box := T.remaining_mem_box
  interval_mem_box := T.interval_mem_box

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Joint measurability in clocks, localization variables and an arbitrary measurable character. -/
theorem MomentumTreeData.stronglyMeasurable_coupleSpatialFrequency {d n m w : ℕ}
    {α : Type*} [MeasurableSpace α] (P : MomentumTreeData n m w)
    (ν : α → PairedMomentum d n) (hν : Measurable ν)
    {χ : ℝ → ℝ} (hχ : Measurable χ) (R : RootCoordinates n) {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ)) (hI : MeasurableSet I)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ)) :
    StronglyMeasurable (fun v : (Fin 2 → ℝ) ×
      ((SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) × α) =>
        (MomentumTreeData.allCellCutoffCoupleKernelSpatial (P := P)) χ R L γ δ (spatialFrequencyLinks Q (ν v.2.2)) I S v.1 v.2.1) := by
  have he (t : Fin 2 → ℝ) (u : SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) (a : α) :
      (MomentumTreeData.allCellCutoffCoupleKernelSpatial (P := P)) χ R L γ δ (spatialFrequencyLinks Q (ν a)) I S t u =
        (MomentumTreeData.allCellCutoffCoupleKernelSpatial (P := P)) χ R L γ δ (spatialFrequencyLinks Q 0) I S t
          (u.1, u.2 + internalFrequency (ν a)) := by
    unfold allCellCutoffCoupleKernelSpatial
    rw [(MomentumTreeData.spectralLinksSpatial_frequency (P := P))]
  simp_rw [he]
  exact ((MomentumTreeData.stronglyMeasurable_allCellCutoffCoupleKernelSpatial (P := P)) hχ R hL γ δ
    (spatialFrequencyLinks Q 0) I hI S).comp_measurable
      (g := fun v : (Fin 2 → ℝ) ×
        ((SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) × α) =>
        (v.1, (v.2.1.1, v.2.1.2 + internalFrequency (ν v.2.2))))
      (measurable_fst.prodMk
        (((measurable_fst.comp measurable_fst).comp measurable_snd).prodMk
          (((measurable_snd.comp measurable_fst).comp measurable_snd).add
            ((continuous_internalFrequency (d := d) (n := n) (m := m)).measurable.comp
              (hν.comp (measurable_snd.comp measurable_snd))))))

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Joint measurability in clocks, localization variables and an arbitrary measurable character. -/
theorem MomentumTreeData.stronglyMeasurable_treeSpatialFrequency {d n m w : ℕ}
    {α : Type*} [MeasurableSpace α] (P : MomentumTreeData n m w)
    (ν : α → PairedMomentum d n) (hν : Measurable ν)
    {χ : ℝ → ℝ} (hχ : Measurable χ) (R : RootCoordinates n) {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ)) (hI : MeasurableSet I)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ)) :
    StronglyMeasurable (fun v : (Fin 2 → ℝ) ×
      ((SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) × α) =>
        (MomentumTreeData.allCellTreeKernelSpatial (P := P)) R χ L γ δ (spatialFrequencyLinks Q (ν v.2.2)) I S v.1 v.2.1) := by
  have he (t : Fin 2 → ℝ) (u : SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) (a : α) :
      (MomentumTreeData.allCellTreeKernelSpatial (P := P)) R χ L γ δ (spatialFrequencyLinks Q (ν a)) I S t u =
        (MomentumTreeData.allCellTreeKernelSpatial (P := P)) R χ L γ δ (spatialFrequencyLinks Q 0) I S t
          (u.1, u.2 + internalFrequency (ν a)) := by
    unfold allCellTreeKernelSpatial
    rw [(MomentumTreeData.spectralLinksSpatial_frequency (P := P))]
  simp_rw [he]
  exact ((MomentumTreeData.stronglyMeasurable_allCellTreeKernelSpatial (P := P)) R hχ hL γ δ
    (spatialFrequencyLinks Q 0) I hI S).comp_measurable
      (g := fun v : (Fin 2 → ℝ) ×
        ((SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) × α) =>
        (v.1, (v.2.1.1, v.2.1.2 + internalFrequency (ν v.2.2))))
      (measurable_fst.prodMk
        (((measurable_fst.comp measurable_fst).comp measurable_snd).prodMk
          (((measurable_snd.comp measurable_fst).comp measurable_snd).add
            ((continuous_internalFrequency (d := d) (n := n) (m := m)).measurable.comp
              (hν.comp (measurable_snd.comp measurable_snd))))))

end WaveTurbulence.Flower.IncTop