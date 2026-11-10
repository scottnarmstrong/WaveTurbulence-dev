/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.AllCellCutoffCoupleFamily
public import WaveTurbulence.Foundations.Incoh.CouplePhysicalL1
public import WaveTurbulence.Foundations.Incoh.UniformL1MixtureIntegrability
public import WaveTurbulence.Foundations.Incoh.CouplePointwiseL1
public import WaveTurbulence.Foundations.Incoh.PointwiseMixtureIntegrability
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import WaveTurbulence.Foundations.Incoh.RawSourceCellIntegral
public import WaveTurbulence.Foundations.Incoh.OneClockCouple

/-! # Exact raw source recovery for a couple with one genuine root clock

TARGET L1049, audit P-1. The passive external time is removed from the
source domain. The auxiliary selected branching clock is fully integrated.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Literal raw source operator with only its actual external root constraint. -/
@[expose] def MomentumTreeData.sourceOneClockKernel {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (R : RootCoordinates n) (a : Fin 2)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (f : Fin m → Mom d → ℂ) (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  P.sourceIntegral ζ L γ δ Q (I ∩ R.oneClockCut a (t a)) f k

end WaveTurbulence.Incoh
