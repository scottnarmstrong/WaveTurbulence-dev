/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec


/-! # `Cut2A.SpatialMeasure`, definitions only

Definitions-only split of C2-A's `Cut2A.SpatialMeasure` (integrable Fourier-measure presentations): the structure
`SpatialMeasure` and `SpatialMeasure.mass`, `SpatialMeasure.value`, `SpatialMeasure.measure`.  Bodies are verbatim from
c2a `Cut2A/SpatialMeasure.lean`; its theorems and `SpatialMeasure.product` are not ported here.  When C2-A lands, its
`Cut2A.SpatialMeasure` must import this module and drop its copies. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace WaveTurbulence.Cut2A
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
variable (α : Type*) [MeasurableSpace α]

/-- A finite Fourier measure presented as the pushforward of an integrable density.
The parameter space need not be the frequency space, so affine maps may lose rank. -/
structure SpatialMeasure where
  μ : Measure α
  sigmaFinite : SigmaFinite μ
  frequency : α → V
  frequency_measurable : Measurable frequency
  amplitude : α → ℂ
  amplitude_integrable : Integrable amplitude μ

variable {V α}
instance (F : SpatialMeasure V α) : SigmaFinite F.μ := F.sigmaFinite

def SpatialMeasure.mass (F : SpatialMeasure V α) : ℝ := ∫ a, ‖F.amplitude a‖ ∂F.μ

def SpatialMeasure.value (F : SpatialMeasure V α) (x : V) : ℂ :=
  ∫ a, F.amplitude a * (Real.fourierChar (inner ℝ (F.frequency a) x) : ℂ) ∂F.μ

end WaveTurbulence.Cut2A
