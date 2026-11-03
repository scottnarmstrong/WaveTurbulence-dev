/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.SchwartzSmooth
public import WaveTurbulence.Foundations.Resonant.EnergyBilinear
public import WaveTurbulence.Foundations.Resonant.NTOmegainvSource

/-!
# Resonant integrals and inverse-energy principal values

Packet N5's interface: the collision-compatible resonant integral, its
mollified characterization, decay bounds and smooth momentum dependence;
the proved-limit definition of the inverse-energy principal value; and
both parts of DH21 Lemma 6.3 for the square torus.
-/

public section
