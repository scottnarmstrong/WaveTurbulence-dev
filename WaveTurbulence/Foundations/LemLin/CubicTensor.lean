/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LemLin.ScalarLattice
public import WaveTurbulence.Foundations.Fourier.CutoffMultiplication
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Tensor factorization of the cubic integral

We index `ℝ^(3d)` by spatial coordinate first, then by `x,y,z`. Product
Lebesgue measure is unchanged by this grouping. The displayed definition
uses the three source tensor cutoffs and the sum of the coordinate phases.
-/

public section

namespace WaveTurbulence.LemLin
open MeasureTheory Finset
open scoped Classical

/-- The scalar amplitude family supplied by the fixed source cutoff. -/
@[expose] noncomputable def fixedCubicCutoffs : Fin 3 → ScalarCutoff := fun _ => fixedScalarCutoff

end WaveTurbulence.LemLin
