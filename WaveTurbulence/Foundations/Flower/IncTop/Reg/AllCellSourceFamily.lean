/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SourceCellMassBound
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SpectralCoupleMeasurability
public import WaveTurbulence.Foundations.Incoh.CoupleExtensionAgreement

/-! Ported by source from C2-B-TOP `Cut2BReg.AllCellSourceFamily` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.

# The literal source family over every selected localization cell

The countable cell index is discrete; spectral dependence is the actual
continuous Fourier family already proved for each cell.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- Actual signed source amplitude over every selected leaf/link cell. -/
@[expose] def MomentumTreeData.allCellSpectralAmplitudeSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ)) (k : Mom d)
    (u : SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) : ℂ :=
  (MomentumTreeData.sourceSpectralAmplitudeSpatial (P := P)) ζ f u.1.1 u.1.2.val k u.2

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The actual scalar link extension over every selected localization cell. -/
@[expose] def MomentumTreeData.allCellCoupleKernelSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (R : RootCoordinates n) (L γ δ : ℝ)
    (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (t : Fin 2 → ℝ) (u : SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) : ℂ :=
  R.coupleExtension rootCutoff L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.1.2.val u.2) I t

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Actual amplitude strong measurability on the full countable localization measure. -/
theorem MomentumTreeData.stronglyMeasurable_allCellSpectralAmplitudeSpatial {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {B : ℝ} (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (k : Mom d) :
    StronglyMeasurable ((MomentumTreeData.allCellSpectralAmplitudeSpatial (P := P)) ζ f S k) := by
  apply Measurable.stronglyMeasurable
  apply measurable_from_prod_countable_right
  intro u
  exact ((MomentumTreeData.continuous_sourceSpectralAmplitudeSpatial (P := P)) ζ f u.1 u.2.val hK hB h k).measurable

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Joint clock/spectral measurability of the full countable scalar kernel family. -/
theorem MomentumTreeData.stronglyMeasurable_allCellCoupleKernelSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (R : RootCoordinates n) {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ)) (hI : MeasurableSet I)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ)) :
    StronglyMeasurable (fun v : (Fin 2 → ℝ) ×
      (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) =>
        (MomentumTreeData.allCellCoupleKernelSpatial (P := P)) R L γ δ Q I S v.1 v.2) := by
  have hm : Measurable (fun v : SourceCellIndex S ×
      ((Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ)) =>
      R.coupleExtension rootCutoff L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q v.1.2.val v.2.2) I v.2.1) := by
    apply measurable_from_prod_countable_right
    intro u
    exact ((MomentumTreeData.stronglyMeasurable_spectral_coupleExtensionSpatial (P := P)) R hL γ δ Q u.2.val hI
      contDiff_rootCutoff.continuous.measurable).measurable
  have hg : Measurable (fun v : (Fin 2 → ℝ) ×
      (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) =>
        (v.2.1, (v.1, v.2.2))) := by fun_prop
  exact (hm.comp hg).stronglyMeasurable

end WaveTurbulence.Flower.IncTop