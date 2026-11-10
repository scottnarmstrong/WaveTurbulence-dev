/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.ProductMixture
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.AllCellMaskedCoupleDecay
public import WaveTurbulence.Foundations.Incoh.CoupleCutoffUniformDecay

/-! Ported by source from C2-B-TOP `Cut2BReg.WeightedCoupleExtension` (sha256 in COPIED-SHA256SUMS); mechanical edits only.
 # Full couple derivative bounds for actual Fourier-measure spectral extensions -/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- One common spectral extension, with the Fourier parameter inside the spectral integral. -/
@[expose] def MomentumTreeData.fourierMaskedSourceCoupleExtension {d n m w : ℕ} {α : Type}
    [MeasurableSpace α] (P : MomentumTreeData n m w) (F : Cut2A.SpatialMeasure (PairedMomentum d n) α)
    (χ : ℝ → ℝ) (ζ : Circle) (R : RootCoordinates n) (L γ δ : ℝ)
    (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ)) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (τ t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  ∫ u, F.amplitude u.2 * (MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S k u.1 *
    (MomentumTreeData.allCellCutoffCoupleKernelSpatial (P := P)) χ R L γ δ (spatialFrequencyLinks Q (F.frequency u.2)) I S
      (t + τ) u.1 ∂(sourceCellMeasure S).prod F.μ

end WaveTurbulence.Flower.IncTop