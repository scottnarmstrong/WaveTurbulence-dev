/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SourceCellMassBound
public import WaveTurbulence.Foundations.Incoh.SpectralCoupleMeasurability
public import WaveTurbulence.Foundations.Incoh.RootCutoff
public import WaveTurbulence.Foundations.Incoh.RootCumulativeLocal
public import WaveTurbulence.Foundations.Incoh.TwoTimeBoxIntegral
public import WaveTurbulence.Foundations.Incoh.SpectralTreeMeasurability
public import WaveTurbulence.Foundations.Incoh.ParameterTreeDecay

/-! # Actual all-cell causal tree kernels with an arbitrary fixed smooth cutoff -/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The actual scalar link extension over every selected localization cell. -/
@[expose] def MomentumTreeData.allCellTreeKernel {d n m w : ℕ}
    (P : MomentumTreeData n m w) (R : RootCoordinates n) (χ : ℝ → ℝ) (L γ δ : ℝ)
    (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (t : Fin 2 → ℝ) (u : SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) : ℂ :=
  Fourier.cutoffTriangleIntegral χ (R.linkDensity L γ δ (P.spectralLinks Q u.1.2.val u.2) I) t

/-- Joint clock/spectral measurability of the full countable scalar kernel family. -/
theorem MomentumTreeData.stronglyMeasurable_allCellTreeKernel {d n m w : ℕ}
    (P : MomentumTreeData n m w) (R : RootCoordinates n) {χ : ℝ → ℝ} (hχ : Measurable χ) {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ)) (hI : MeasurableSet I)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ)) :
    StronglyMeasurable (fun v : (Fin 2 → ℝ) ×
      (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) =>
        P.allCellTreeKernel R χ L γ δ Q I S v.1 v.2) := by
  have hm : Measurable (fun v : SourceCellIndex S ×
      ((Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ)) =>
      Fourier.cutoffTriangleIntegral χ (R.linkDensity L γ δ (P.spectralLinks Q v.1.2.val v.2.2) I) v.2.1) := by
    apply measurable_from_prod_countable_right
    intro u
    exact (P.stronglyMeasurable_spectral_treeExtension R hL γ δ Q u.2.val hI
      hχ).measurable
  have hg : Measurable (fun v : (Fin 2 → ℝ) ×
      (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) =>
        (v.2.1, (v.1, v.2.2))) := by fun_prop
  exact (hm.comp hg).stronglyMeasurable

end WaveTurbulence.Incoh
