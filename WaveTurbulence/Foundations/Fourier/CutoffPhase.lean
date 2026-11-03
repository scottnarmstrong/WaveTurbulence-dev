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

/-- TARGET L966, L1550: the fixed cutoff's translated non-stationary bound. -/
theorem chi0_nonstationary_phase {d : ℕ} (N : ℕ) (a w : EuclideanSpace ℝ (Fin d)) :
    ‖∫ x, Real.fourierChar (inner ℝ x w) • chi0TensorComplex (ofLp (x - a))‖ ≤
      nonstationaryConstant N (chi0MomSchwartz d) / Real.sqrt (1 + ‖w‖ ^ 2) ^ N := by
  simpa only [chi0MomSchwartz_apply] using
    nonstationary_phase_japanese N (chi0MomSchwartz d) a w

/-- TARGET L968; DH23 L1013ff: `⟨s⟩^{-d}` for the fixed tensor cutoff,
uniformly over all four translations and linear-frequency vectors. -/
theorem chi0_bilinear_stationary_phase {d : ℕ} (hd : 0 < d)
    (a b ξ ζ : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    ‖bilinearPhaseIntegral (chi0MomSchwartz d) (chi0MomSchwartz d) a b ξ ζ s‖ ≤
      bilinearPhaseConstant (chi0MomSchwartz d) (chi0MomSchwartz d) /
        Real.sqrt (1 + s ^ 2) ^ d := by
  simpa only [finrank_euclideanSpace_fin] using
    bilinear_stationary_phase (chi0MomSchwartz d) (chi0MomSchwartz d)
      (by simpa only [finrank_euclideanSpace_fin] using hd) a b ξ ζ s

end WaveTurbulence.Fourier
