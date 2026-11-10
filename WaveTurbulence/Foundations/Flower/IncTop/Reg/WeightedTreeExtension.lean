/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.ProductMixture
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.TreeRootSpatialDecay

/-! Ported by source from C2-B-TOP `Cut2BReg.WeightedTreeExtension` (sha256 in COPIED-SHA256SUMS); mechanical edits only.
 # Full tree derivatives for actual Fourier-measure spectral extensions -/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- The common tree extension on the product source/character measure. -/
@[expose] def MomentumTreeData.fourierRootPartitionSourceTreeExtension {d n m w : ℕ} {α : Type}
    [MeasurableSpace α] (P : MomentumTreeData n m w) (F : Cut2A.SpatialMeasure (PairedMomentum d n) α)
    (ζ : Circle) (R : RootCoordinates n) (χ : ℝ → ℝ) (L γ δ : ℝ)
    (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ)) (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  ∫ u, F.amplitude u.2 * rootAmplitudeSumSpatial ((MomentumTreeData.treeRootSpectralAmplitudeSpatial (P := P)) ζ f S) k u.1 *
    (MomentumTreeData.allCellTreeKernelSpatial (P := P.withRootInput)) R χ L γ δ (spatialFrequencyLinks Q (F.frequency u.2)) I S
      t u.1 ∂(sourceCellMeasure S).prod F.μ

end WaveTurbulence.Flower.IncTop