/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SpectralCoupleMeasurability
public import WaveTurbulence.Foundations.Incoh.CouplePhysicalL1
public import WaveTurbulence.Foundations.Incoh.UniformL1MixtureIntegrability
public import WaveTurbulence.Foundations.Incoh.RootCutoff
public import WaveTurbulence.Foundations.Incoh.RootCumulativeLocal
public import WaveTurbulence.Foundations.Incoh.TwoTimeBoxIntegral
public import WaveTurbulence.Foundations.Incoh.CouplePointwiseL1
public import WaveTurbulence.Foundations.Incoh.PointwiseMixtureIntegrability
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.RawSourceCellIntegral

/-! Ported by source from C2-B-TOP `Cut2BReg.RawCoupleAgreement` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.

# Exact agreement of the recombined extension with the raw source couple

The source kernel is the original unlocalized normalized lattice/time
operator with its two literal external root constraints. Agreement is
pointwise on the whole source box, including its boundary.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- The literal raw source couple kernel with genuine external root-clock constraints. -/
@[expose] def MomentumTreeData.sourceCoupleKernelSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (f : Fin m → Mom d → ℂ) (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  (MomentumTreeData.sourceIntegralSpatial (P := P)) ζ L γ δ Q (I ∩ R.rootCut t) f k

end WaveTurbulence.Flower.IncTop