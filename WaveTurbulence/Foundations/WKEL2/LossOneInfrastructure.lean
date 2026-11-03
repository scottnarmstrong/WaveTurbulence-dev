/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.LossOneSpherical
public import WaveTurbulence.Foundations.WKEL2.TwoAxes
public import WaveTurbulence.Foundations.WKEL2.ScalarShear
public import WaveTurbulence.Foundations.WKEL2.SineMassEstimate
public import WaveTurbulence.Foundations.WKEL2.NonnegativeSquare
public import WaveTurbulence.Foundations.WKEL2.RaySample
public import WaveTurbulence.Foundations.WKEL2.ResonantSupport

/-!
# Infrastructure for research-note Proposition 6

The spherical-average formula, two-axis slicing geometry, scalar Jacobian,
nonnegative square expansion, and the M₁ angular Schur estimate.
-/

public section
