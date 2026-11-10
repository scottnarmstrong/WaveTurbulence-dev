/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.RootAmplitudeMixture
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.TreeRootSpectralMass
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.AllCellTreeFamily
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.MovingTreeFamily

/-! Ported by source from C2-B-TOP `Cut2BReg.TreeRootSpatialDecay` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.
 # Full spatial derivatives of the actual tree source extension -/

public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- The actual common spectral extension, with the locally finite root partition in its amplitude. -/
@[expose] def MomentumTreeData.rootPartitionSourceTreeExtensionSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (R : RootCoordinates n) (χ : ℝ → ℝ)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  ∫ u, rootAmplitudeSumSpatial ((MomentumTreeData.treeRootSpectralAmplitudeSpatial (P := P)) ζ f S) k u *
    (MomentumTreeData.allCellTreeKernelSpatial (P := P.withRootInput)) R χ L γ δ Q I S t u ∂sourceCellMeasure S

end WaveTurbulence.Flower.IncTop