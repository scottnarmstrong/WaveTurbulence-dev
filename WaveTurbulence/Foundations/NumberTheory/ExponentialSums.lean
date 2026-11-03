/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.SawtoothFourier
public import WaveTurbulence.Foundations.NumberTheory.DerivativeTests
public import WaveTurbulence.Foundations.NumberTheory.WeylDifferencing

/-!
# Exponential-sum toolkit

NT-CIRCLE-v2, goal 1: the right-continuous sawtooth and its Fourier truncation
with explicit error, continuous and discrete first- and second-derivative
tests, and Weyl–van der Corput differencing with exact integer overlaps.
This module contains no circle discrepancy estimate or B-process.
-/

public section
