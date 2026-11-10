/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.BilinearPhase
public import WaveTurbulence.Foundations.Fourier.CutoffMultiplication
import Mathlib.Tactic

/-!
# Phase bounds for the paper's fixed tensor cutoff

TARGET L966, L968, L1550. The generic translated Fourier and bilinear
phase estimates are instantiated with the explicit AN-FOURIER cutoff.
The constants depend only on the dimension (and derivative order in the
non-stationary estimate), never on translations or linear frequencies.
-/

public section

open MeasureTheory WithLp
open scoped SchwartzMap ContDiff

namespace WaveTurbulence.Fourier

/-- The fixed tensor cutoff, bundled as a Schwartz function in Euclidean
momentum coordinates. No extra regularity assumption is supplied by users. -/
@[expose] noncomputable def chi0MomSchwartz (d : ℕ) : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) :=
  ((chi0TensorComplex_hasCompactSupport d).comp_homeomorph
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toHomeomorph).toSchwartzMap
    (chi0TensorComplex_contDiff.comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).contDiff)

@[simp] theorem chi0MomSchwartz_apply {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    chi0MomSchwartz d x = chi0TensorComplex (ofLp x) := rfl

end WaveTurbulence.Fourier
