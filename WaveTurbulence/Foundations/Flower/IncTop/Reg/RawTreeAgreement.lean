/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.MovingTreeFamily
public import WaveTurbulence.Foundations.Incoh.ParameterTreeDecay
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SpectralTreeClocks
public import WaveTurbulence.Foundations.Incoh.CutoffPointwiseL1
public import WaveTurbulence.Foundations.Incoh.PointwiseMixtureIntegrability
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.RawSourceCellIntegral

/-! Ported by source from C2-B-TOP `Cut2BReg.RawTreeAgreement` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.

# Exact raw source agreement of the moving-cell tree extension

The finite cover need only cover each actual root momentum separately.
Pointwise Fubini and the actual causal source identity identify the full
moving-cell spectral extension with the raw unlocalized source operator.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- The literal raw source tree kernel with its original external causal root constraints. -/
@[expose] def MomentumTreeData.sourceTreeKernelSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (f : Fin m → Mom d → ℂ) (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  (MomentumTreeData.sourceIntegralSpatial (P := P)) ζ L γ δ Q (I ∩ R.causalRootCut t) f k

end WaveTurbulence.Flower.IncTop