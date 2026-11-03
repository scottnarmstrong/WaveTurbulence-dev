/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.MainGlue.InductionParameters
public import WaveTurbulence.Foundations.MainGlue.SchwartzMass
public import WaveTurbulence.Foundations.MainGlue.Observable

/-!
# Wave-B-independent inputs for sealing Theorem 1.1

SEAL-PLAN §B.4: G1 (Borel smooth-data set), G2 (measurable Fourier-energy
observable), G5 (Gaussian law packaging), G6 (mass-event bound), G7 (Schwartz
lattice mass), and G10(a,b,c) (parameters and absorption). This interface
imports only proved infrastructure and frozen definitions. The absorption
threshold explicitly retains its necessary dependence on induction length.
-/

public section
