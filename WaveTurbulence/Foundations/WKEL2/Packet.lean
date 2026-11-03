/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.AngularCoordinates
public import WaveTurbulence.Foundations.WKEL2.Trilinear
public import WaveTurbulence.Foundations.WKEL2.Blowup
public import WaveTurbulence.Foundations.WKEL2.MaximalTimeEquality
public import WaveTurbulence.Foundations.WKEL2.JetClosedIdentity
public import WaveTurbulence.Foundations.WKEL2.CanonicalJetEquivalence
public import WaveTurbulence.Foundations.WKEL2.SolutionEquivalence
public import WaveTurbulence.Foundations.WKEL2.SchwartzPicard

/-!
# WKE-L2S: general-dimensional weighted L² estimates and the full blow-up criterion

The research note's Lemmas 1–4, Propositions 5–7, and Theorem 7 hold for
`d ≥ 3`, `s > d/2 - 1`. The source norm is the exact frozen `weightedL2Norm`.
The ensuing Banach Picard theory, finite-jet persistence, actual Schwartz
reconstruction, and maximal-time identification prove TARGET Appendix C's
full blow-up passage relative to the landed `WKE.tauMax`.

The completed coordinate identities, exact mild/source solution equivalence,
and equivalence of the finite weighted-jet and Schwartz topologies discharge
the three supporting obligations in the research-note audit, §3.
-/

public section
