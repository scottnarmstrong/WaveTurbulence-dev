/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Foundations.Counting.CircleArc
public import WaveTurbulence.Foundations.Counting.ExponentAudit
public import WaveTurbulence.Foundations.Counting.LatticeDisc
public import WaveTurbulence.Foundations.Cumulant.Basic
public import WaveTurbulence.Foundations.Cumulant.Inversion
public import WaveTurbulence.Foundations.Cumulant.PartitionRecursion
public import WaveTurbulence.Foundations.Cumulant.Symmetry
public import WaveTurbulence.Foundations.Gaussian.BooleanCube
public import WaveTurbulence.Foundations.Gaussian.ComplexGaussian
public import WaveTurbulence.Foundations.Gaussian.CubeToGaussian
public import WaveTurbulence.Foundations.Gaussian.FiniteAverage
public import WaveTurbulence.Foundations.Gaussian.Hypercontractivity
public import WaveTurbulence.Foundations.Gaussian.Isserlis
public import WaveTurbulence.Foundations.Gaussian.IsserlisMoments
public import WaveTurbulence.Foundations.Gaussian.IsserlisPairings
public import WaveTurbulence.Foundations.Gaussian.IsserlisPartitions
public import WaveTurbulence.Foundations.Gaussian.IsserlisPolynomial
public import WaveTurbulence.Foundations.Gaussian.LargeDeviation
public import WaveTurbulence.Foundations.Gaussian.MomentLimit
public import WaveTurbulence.Foundations.Gaussian.TwoPoint
public import WaveTurbulence.Foundations.NumberTheory.DerivativeTests
public import WaveTurbulence.Foundations.NumberTheory.Differencing
public import WaveTurbulence.Foundations.NumberTheory.ExponentialSums
public import WaveTurbulence.Foundations.NumberTheory.HalfPowerSums
public import WaveTurbulence.Foundations.NumberTheory.IntegerDistance
public import WaveTurbulence.Foundations.NumberTheory.KusminLandau
public import WaveTurbulence.Foundations.NumberTheory.Phase
public import WaveTurbulence.Foundations.NumberTheory.Sawtooth
public import WaveTurbulence.Foundations.NumberTheory.SawtoothFourier
public import WaveTurbulence.Foundations.NumberTheory.SawtoothSmoothing
public import WaveTurbulence.Foundations.NumberTheory.SecondDifference
public import WaveTurbulence.Foundations.NumberTheory.SineSeries
public import WaveTurbulence.Foundations.NumberTheory.SmoothingFourier
public import WaveTurbulence.Foundations.NumberTheory.WeylDifferencing
public import WaveTurbulence.Foundations.Torus.Basic
public import WaveTurbulence.Foundations.Torus.Derivative
public import WaveTurbulence.Foundations.Torus.Inversion
public import WaveTurbulence.Foundations.Torus.Product
public import WaveTurbulence.Foundations.Torus.Series
public import WaveTurbulence.Foundations.Torus.TimeDerivative
public import WaveTurbulence.Foundations.WeylSums.Basic
public import WaveTurbulence.Foundations.WeylSums.Differencing
public import WaveTurbulence.Foundations.WeylSums.Dirichlet
public import WaveTurbulence.Foundations.WeylSums.Geometric
public import WaveTurbulence.Foundations.WeylSums.RationalSpacing
public import WaveTurbulence.Frozen.Defs.CollisionOp
public import WaveTurbulence.Frozen.Defs.InitialCoeff
public import WaveTurbulence.Frozen.Defs.IsSmoothNLSSolution
public import WaveTurbulence.Frozen.Defs.IsWKESolution
public import WaveTurbulence.Frozen.Defs.KineticTime
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.NormLaplacian
public import WaveTurbulence.Frozen.Defs.PartialDeriv
public import WaveTurbulence.Frozen.Defs.SolvableEvent
public import WaveTurbulence.Frozen.Defs.StdComplexGaussian
public import WaveTurbulence.Frozen.Defs.TorusFourierCoeff
public import WaveTurbulence.Frozen.Defs.WeightedL2Norm

/-!
# WaveTurbulence

Root of the Lean formalization of Y. Deng and Z. Hani, *Long time justification of wave
turbulence theory*, arXiv:2311.10082v2.
-/
