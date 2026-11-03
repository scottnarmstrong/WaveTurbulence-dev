/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.LeibnizInterval
public import WaveTurbulence.Frozen.Defs.PartialDeriv
public import WaveTurbulence.Foundations.Torus.Derivative
import Mathlib.Tactic

/-!
# The rectangular time primitive and its boundary derivatives

The mixed endpoint derivative is the original amplitude. All integrals
are oriented, so no positivity of either endpoint is assumed.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace WaveTurbulence.Fourier

/-- Rectangular integration from the origin. -/
@[expose] noncomputable def rectanglePrimitive (A : (Fin 2 → ℝ) → ℂ)
    (t : Fin 2 → ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..t 0, ∫ v in (0 : ℝ)..t 1, A ![u, v]

/-- Smooth amplitudes give smooth rectangular primitives. -/
theorem rectanglePrimitive_contDiff {A : (Fin 2 → ℝ) → ℂ} (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (rectanglePrimitive A) := by
  apply contDiff_intervalIntegral (G := fun p : (Fin 2 → ℝ) × ℝ =>
    ∫ v in (0 : ℝ)..p.1 1, A ![p.2, v]) ?_ contDiff_const (by fun_prop)
  apply contDiff_intervalIntegral (G := fun p : ((Fin 2 → ℝ) × ℝ) × ℝ =>
    A ![p.1.2, p.2]) ?_ contDiff_const (by fun_prop)
  apply hA.comp
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · change ContDiff ℝ ∞ (fun p : ((Fin 2 → ℝ) × ℝ) × ℝ => p.1.2)
    fun_prop
  · change ContDiff ℝ ∞ (fun p : ((Fin 2 → ℝ) × ℝ) × ℝ => p.2)
    fun_prop

/-- Upper endpoint differentiation exposes a row of the amplitude. -/
theorem partialDeriv_rectanglePrimitive_zero {A : (Fin 2 → ℝ) → ℂ}
    (hA : ContDiff ℝ ∞ A) (t : Fin 2 → ℝ) :
    WaveTurbulence.partialDeriv 0 (rectanglePrimitive A) t =
      ∫ v in (0 : ℝ)..t 1, A ![t 0, v] := by
  have hg : ContDiff ℝ ∞ (fun u : ℝ => ∫ v in (0 : ℝ)..t 1, A ![u, v]) := by
    apply contDiff_intervalIntegral (G := fun p : ℝ × ℝ => A ![p.1, p.2])
      ?_ contDiff_const contDiff_const
    apply hA.comp
    apply contDiff_pi.mpr
    intro j
    fin_cases j
    · change ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.1)
      fun_prop
    · change ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.2)
      fun_prop
  have hd := intervalIntegral.integral_hasDerivAt_right (hg.continuous.intervalIntegrable 0 (t 0))
    hg.continuous.stronglyMeasurable.stronglyMeasurableAtFilter hg.continuous.continuousAt
  simpa only [WaveTurbulence.partialDeriv, rectanglePrimitive, Function.update_self,
    Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)] using hd.deriv

/-- Lower coordinate differentiation exposes a column of the amplitude. -/
theorem partialDeriv_rectanglePrimitive_one {A : (Fin 2 → ℝ) → ℂ}
    (hA : ContDiff ℝ ∞ A) (t : Fin 2 → ℝ) :
    WaveTurbulence.partialDeriv 1 (rectanglePrimitive A) t =
      ∫ u in (0 : ℝ)..t 0, A ![u, t 1] := by
  let G : ℝ × ℝ → ℂ := fun p => ∫ v in (0 : ℝ)..p.1, A ![p.2, v]
  have hG : ContDiff ℝ ∞ G := by
    apply contDiff_intervalIntegral (G := fun p : (ℝ × ℝ) × ℝ => A ![p.1.2, p.2])
      ?_ contDiff_const (by fun_prop)
    apply hA.comp
    apply contDiff_pi.mpr
    intro j
    fin_cases j
    · change ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => p.1.2)
      fun_prop
    · change ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => p.2)
      fun_prop
  have hd := hasDerivAt_fixed_interval hG (t 1) (0 : ℝ) (t 0)
  have he (u : ℝ) : fderiv ℝ G (t 1, u) (1, 0) = A ![u, t 1] := by
    have hrow : Continuous (fun v : ℝ => A ![u, v]) := by
      apply hA.continuous.comp
      fun_prop
    have hFTC := intervalIntegral.integral_hasDerivAt_right (hrow.intervalIntegrable 0 (t 1))
      hrow.stronglyMeasurable.stronglyMeasurableAtFilter hrow.continuousAt
    have hc := (hG.differentiable (by simp) (t 1, u)).hasFDerivAt.comp_hasDerivAt (t 1)
      ((hasDerivAt_id (t 1)).prodMk (hasDerivAt_const (t 1) u))
    exact hc.unique hFTC
  simp_rw [he] at hd
  simpa only [WaveTurbulence.partialDeriv, rectanglePrimitive, Function.update_self,
    Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide)] using hd.deriv

/-- The mixed derivative recovers the amplitude at the output point. -/
theorem partialDeriv_rectanglePrimitive_mixed {A : (Fin 2 → ℝ) → ℂ}
    (hA : ContDiff ℝ ∞ A) (t : Fin 2 → ℝ) :
    WaveTurbulence.partialDeriv 0 (WaveTurbulence.partialDeriv 1 (rectanglePrimitive A)) t =
      A t := by
  have he : WaveTurbulence.partialDeriv 1 (rectanglePrimitive A) =
      fun t => ∫ u in (0 : ℝ)..t 0, A ![u, t 1] :=
    funext (partialDeriv_rectanglePrimitive_one hA)
  rw [he]
  have hcol : Continuous (fun u : ℝ => A ![u, t 1]) := by
    apply hA.continuous.comp
    fun_prop
  have hd := intervalIntegral.integral_hasDerivAt_right (hcol.intervalIntegrable 0 (t 0))
    hcol.stronglyMeasurable.stronglyMeasurableAtFilter hcol.continuousAt
  have ht : ![t 0, t 1] = t := by ext j; fin_cases j <;> rfl
  simpa only [WaveTurbulence.partialDeriv, Function.update_self,
    Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), ht] using hd.deriv

/-- Smoothness of the exposed row primitive. -/
theorem rectangle_row_contDiff {A : (Fin 2 → ℝ) → ℂ} (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (fun t : Fin 2 → ℝ => ∫ v in (0 : ℝ)..t 1, A ![t 0, v]) := by
  have he : WaveTurbulence.partialDeriv 0 (rectanglePrimitive A) =
      (fun t : Fin 2 → ℝ => ∫ v in (0 : ℝ)..t 1, A ![t 0, v]) :=
    funext (partialDeriv_rectanglePrimitive_zero hA)
  rw [← he]
  exact WaveTurbulence.contDiff_infty_partialDeriv (rectanglePrimitive_contDiff hA) 0

/-- Smoothness of the exposed column primitive. -/
theorem rectangle_column_contDiff {A : (Fin 2 → ℝ) → ℂ} (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (fun t : Fin 2 → ℝ => ∫ u in (0 : ℝ)..t 0, A ![u, t 1]) := by
  have he : WaveTurbulence.partialDeriv 1 (rectanglePrimitive A) =
      (fun t : Fin 2 → ℝ => ∫ u in (0 : ℝ)..t 0, A ![u, t 1]) :=
    funext (partialDeriv_rectanglePrimitive_one hA)
  rw [← he]
  exact WaveTurbulence.contDiff_infty_partialDeriv (rectanglePrimitive_contDiff hA) 1

end WaveTurbulence.Fourier
