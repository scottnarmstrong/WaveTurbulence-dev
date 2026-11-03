/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.ExponentPair
public import WaveTurbulence.Foundations.VdCB.EulerSummation
public import WaveTurbulence.Foundations.VdCB.PairedHarmonic
public import WaveTurbulence.Foundations.VdCB.SmoothPoisson
public import WaveTurbulence.Foundations.VdCB.NonstationaryBound

/-!
# Basic interfaces for the B-process

This interface collects the stable model/exponent-pair definitions and
proved analytic tools. The sharp truncated Poisson and analytic B-closure
are separate results and are not asserted by this import module.
-/

public section
