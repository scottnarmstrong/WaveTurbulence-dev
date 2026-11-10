/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.MaskedCouplePointwise
public import WaveTurbulence.Foundations.Incoh.RawCoupleAgreement
public import WaveTurbulence.Foundations.Incoh.SourceRootMaskAgreement
public import WaveTurbulence.Foundations.Incoh.CoupleLinkCellLocalization
public import WaveTurbulence.Foundations.Fourier.Norm00VRestriction
public import WaveTurbulence.Foundations.Incoh.FinalExponentLoss
public import WaveTurbulence.Foundations.Incoh.RawOneClockAgreement
public import WaveTurbulence.Foundations.Incoh.OneClockSelection
public import WaveTurbulence.Foundations.Incoh.ParameterTimeTranslation
public import WaveTurbulence.Foundations.Incoh.TreeRootSpatialDecay
public import WaveTurbulence.Foundations.Incoh.MaskedTreePointwise
public import WaveTurbulence.Foundations.Incoh.TreeCoefficientAbsorption

/-!
# TARGET Proposition 5.1 for the finite source carrier

The two actual source norms have one constant and one threshold, independent of source order.
The intrinsic single-root couple result is exported alongside the two-root couple result.
Instantiation with frozen gardens belongs to C2, after the Wave B freeze.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Incoh

/-- Monotonicity in an exponential source constant. -/
theorem sourceRate_mono_constant {C C' δ r : ℝ} (hC : 0 ≤ C) (hle : C ≤ C')
    (hδ : 0 ≤ δ) (hr : 0 ≤ r) (n : ℕ) :
    ENNReal.ofReal ((C * δ) ^ n * r) ≤ ENNReal.ofReal ((C' * δ) ^ n * r) :=
  ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (mul_nonneg hC hδ) (mul_le_mul_of_nonneg_right hle hδ) n) hr)

end WaveTurbulence.Incoh
