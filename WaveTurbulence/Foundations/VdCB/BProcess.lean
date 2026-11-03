/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.Basic
public import WaveTurbulence.Foundations.VdCB.TruncatedPoissonShift
public import WaveTurbulence.Foundations.VdCB.SharpPoisson
public import WaveTurbulence.Foundations.VdCB.BProcessSelected
public import WaveTurbulence.Foundations.VdCB.StationaryFrequencyCount
public import WaveTurbulence.Foundations.VdCB.BProcessScaling
public import WaveTurbulence.Foundations.VdCB.CircleWeightedStationary
public import WaveTurbulence.Foundations.VdCB.CircleWeightedSum
public import WaveTurbulence.Foundations.VdCB.CircleDualWeightedASum
public import WaveTurbulence.Foundations.VdCB.CircleCriticalUniqueness
public import WaveTurbulence.Foundations.VdCB.CircleCountingBridge
public import WaveTurbulence.Foundations.VdCB.CircleFrequencyBounds

/-!
# Checked finite B-process and direct circle-family tools

This interface exports sharp truncated Poisson, sharp stationary phase,
the finite Legendre dual-sum estimate, actual stationary-frequency
selection, and the unconditional actual circle endpoint-block estimate
for `(11/30,16/30)`, including its counting-transfer application.

The shared `IsExponentPair` predicate and its trivial pair are also
exported. Analytic closure under `bTransform` is not asserted here;
`bProcess_scaling` is the exact algebraic scale identity only.
-/

public section
