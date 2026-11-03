/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LemLin.QuadraticDerivative
public import WaveTurbulence.Foundations.LemLin.CoordinateFourier

/-!
# Coordinate derivatives of compact cubic amplitudes

The product rule preserves the fixed amplitude class. The only extra term
is the linear gradient of the quadratic phase, treated by coordinate
multiplication in the subsequent frequency recurrence.
-/

public section

namespace WaveTurbulence.LemLin
open Finset
open scoped Classical ContDiff

/-- Isolate an amplitude changed in one coordinate. -/
theorem cubicProduct_update_family (f : Fin 3 → ScalarCutoff) (p : Fin 3 → ℝ)
    (j : Fin 3) (g : ScalarCutoff) :
    cubicProduct (Function.update f j g) p =
      g (p j) * ∏ i ∈ univ \ {j}, f i (p i) := by
  unfold cubicProduct
  have he : (fun i => Function.update f j g i (p i)) =
      Function.update (fun i => f i (p i)) j (g (p j)) := by
    funext i
    by_cases hi : i = j <;> simp [hi, Function.update]
  rw [he, prod_update_of_mem (mem_univ j)]

/-- Isolate a variable changed in one coordinate. -/
theorem cubicProduct_update_coordinate (f : Fin 3 → ScalarCutoff) (p : Fin 3 → ℝ)
    (j : Fin 3) (u : ℝ) :
    cubicProduct f (Function.update p j u) =
      f j u * ∏ i ∈ univ \ {j}, f i (p i) := by
  unfold cubicProduct
  have he : (fun i => f i (Function.update p j u i)) =
      Function.update (fun i => f i (p i)) j (f j u) := by
    funext i
    by_cases hi : i = j <;> simp [hi, Function.update]
  rw [he, prod_update_of_mem (mem_univ j)]

/-- Differentiation of the cutoff product changes exactly one scalar factor. -/
theorem hasDerivAt_cubicProduct_update (f : Fin 3 → ScalarCutoff)
    (p : Fin 3 → ℝ) (j : Fin 3) :
    HasDerivAt (fun u => cubicProduct f (Function.update p j u))
      (cubicProduct (Function.update f j (f j).differentiate) p) (p j) := by
  have hd := ((f j).smooth.differentiable (by simp) (p j)).hasDerivAt
  have he := hd.mul_const (∏ i ∈ univ \ {j}, f i (p i))
  simpa only [cubicProduct_update_coordinate, cubicProduct_update_family,
    ScalarCutoff.differentiate] using he

/-- Exact coordinate product rule for both quadratic phases. -/
theorem partialDeriv_scalarCubicAmplitude (kind : CubicPhase)
    (f : Fin 3 → ScalarCutoff) (s t : ℝ) (j : Fin 3) (p : Fin 3 → ℝ) :
    partialDeriv j (scalarCubicAmplitude kind f s t) p =
      scalarCubicAmplitude kind (Function.update f j (f j).differentiate) s t p +
        (2 * Real.pi * Complex.I * (cubicFrequencyShift kind s t p j : ℂ)) *
          scalarCubicAmplitude kind f s t p := by
  have hq := hasDerivAt_scalarQuadratic_update kind s t p j
  have hc := (Real.hasDerivAt_fourierChar
    (scalarQuadratic kind s t (Function.update p j (p j)))).scomp (p j) hq
  simp only [Function.update_eq_self] at hc
  have hp := (hasDerivAt_cubicProduct_update f p j).mul hc
  rw [partialDeriv]
  convert hp.deriv using 1
  · rfl
  · simp only [scalarCubicAmplitude, Function.comp_apply, Function.update_eq_self, Complex.real_smul]
    ring

end WaveTurbulence.LemLin
