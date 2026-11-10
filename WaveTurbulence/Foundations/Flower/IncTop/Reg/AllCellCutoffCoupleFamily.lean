/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SourceCellMassBound
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SpectralCoupleMeasurability
public import WaveTurbulence.Foundations.Incoh.RootCutoff
public import WaveTurbulence.Foundations.Incoh.RootCumulativeLocal
public import WaveTurbulence.Foundations.Incoh.TwoTimeBoxIntegral

/-! Ported by source from C2-B-TOP `Cut2BReg.AllCellCutoffCoupleFamily` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.
 # Actual all-cell couple kernels with an arbitrary fixed smooth cutoff -/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- The actual scalar link extension over every selected localization cell. -/
@[expose] def MomentumTreeData.allCellCutoffCoupleKernelSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (χ : ℝ → ℝ) (R : RootCoordinates n) (L γ δ : ℝ)
    (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (t : Fin 2 → ℝ) (u : SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) : ℂ :=
  R.coupleExtension χ L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.1.2.val u.2) I t

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Joint clock/spectral measurability of the full countable scalar kernel family. -/
theorem MomentumTreeData.stronglyMeasurable_allCellCutoffCoupleKernelSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) {χ : ℝ → ℝ} (hχ : Measurable χ) (R : RootCoordinates n) {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ)) (hI : MeasurableSet I)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ)) :
    StronglyMeasurable (fun v : (Fin 2 → ℝ) ×
      (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) =>
        (MomentumTreeData.allCellCutoffCoupleKernelSpatial (P := P)) χ R L γ δ Q I S v.1 v.2) := by
  have hm : Measurable (fun v : SourceCellIndex S ×
      ((Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ)) =>
      R.coupleExtension χ L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q v.1.2.val v.2.2) I v.2.1) := by
    apply measurable_from_prod_countable_right
    intro u
    exact ((MomentumTreeData.stronglyMeasurable_spectral_coupleExtensionSpatial (P := P)) R hL γ δ Q u.2.val hI
      hχ).measurable
  have hg : Measurable (fun v : (Fin 2 → ℝ) ×
      (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) =>
        (v.2.1, (v.1, v.2.2))) := by fun_prop
  exact (hm.comp hg).stronglyMeasurable

end WaveTurbulence.Flower.IncTop