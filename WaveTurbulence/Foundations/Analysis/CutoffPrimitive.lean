/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.TimePrimitive
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Cutoff oscillatory primitives

Regularity and explicit derivatives of the kernel underlying the time
integration operator. Compact support is inherited from the cutoff.
-/

public section

open scoped ContDiff

namespace WaveTurbulence.Analysis

/-- A smooth cutoff times the oscillatory primitive based at `a`. -/
@[expose] noncomputable def cutoffPrimitive (χ : ℝ → ℂ) (a q t : ℝ) : ℂ :=
  χ t * timePrimitive a q t

theorem contDiff_cutoffPrimitive {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ) (a q : ℝ) :
    ContDiff ℝ ∞ (cutoffPrimitive χ a q) := hχ.mul (contDiff_timePrimitive a q)

theorem hasCompactSupport_cutoffPrimitive {χ : ℝ → ℂ} (hχ : HasCompactSupport χ) (a q : ℝ) :
    HasCompactSupport (cutoffPrimitive χ a q) := by
  convert hχ.mul_right (f' := timePrimitive a q) using 1
  ext t
  rfl

/-- First derivative of the cutoff primitive. -/
theorem deriv_cutoffPrimitive {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ) (a q t : ℝ) :
    deriv (cutoffPrimitive χ a q) t =
      deriv χ t * timePrimitive a q t + χ t * timePhase q t := by
  have hh := ((hχ.differentiable (by simp)) t).hasDerivAt.mul (hasDerivAt_timePrimitive a q t)
  have he : HasDerivAt (cutoffPrimitive χ a q)
      (deriv χ t * timePrimitive a q t + χ t * timePhase q t) t := by
    convert hh using 1
    ext s
    rfl
  exact he.deriv

/-- Second derivative of the cutoff primitive. -/
theorem deriv_deriv_cutoffPrimitive {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ) (a q t : ℝ) :
    deriv (deriv (cutoffPrimitive χ a q)) t =
      deriv (deriv χ) t * timePrimitive a q t + 2 * deriv χ t * timePhase q t +
        χ t * ((2 * Real.pi * q : ℂ) * Complex.I) * timePhase q t := by
  have hχ' := (contDiff_infty_iff_deriv.mp hχ).2
  have h1 := ((hχ'.differentiable (by simp)) t).hasDerivAt.mul (hasDerivAt_timePrimitive a q t)
  have h2 := ((hχ.differentiable (by simp)) t).hasDerivAt.mul (hasDerivAt_timePhase q t)
  have hh := h1.add h2
  have he : deriv (cutoffPrimitive χ a q) =
      (fun s => deriv χ s * timePrimitive a q s + χ s * timePhase q s) :=
    funext (deriv_cutoffPrimitive hχ a q)
  rw [he]
  have hh' : HasDerivAt
      (fun s => deriv χ s * timePrimitive a q s + χ s * timePhase q s)
      ((deriv (deriv χ) t * timePrimitive a q t + deriv χ t * timePhase q t) +
        (deriv χ t * timePhase q t + χ t * (((2 * Real.pi * q : ℂ) * Complex.I) * timePhase q t))) t := by
    convert hh using 1
  rw [hh'.deriv]
  ring

end WaveTurbulence.Analysis
