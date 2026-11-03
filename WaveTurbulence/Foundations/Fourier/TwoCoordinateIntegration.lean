/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

/-!
# Iterated integration in two time coordinates

Both integration orders agree with the coordinate Lebesgue measure
used by the paper's time Fourier transform.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Fourier

/-- Coordinate Tonelli formula with the first coordinate integrated outside. -/
theorem lintegral_two_coordinates {f : (Fin 2 → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x) = ∫⁻ u : ℝ, ∫⁻ v : ℝ, f ![u, v] := by
  have hm := volume_preserving_finTwoArrow ℝ
  have he : (fun z : ℝ × ℝ => f ![z.1, z.2]) = f ∘ MeasurableEquiv.finTwoArrow.symm := by
    funext z
    congr 1
  have hmeas : Measurable (fun z : ℝ × ℝ => f ![z.1, z.2]) :=
    hf.comp (by fun_prop)
  calc
    _ = ∫⁻ z : ℝ × ℝ, f (MeasurableEquiv.finTwoArrow.symm z) :=
      (hm.symm.lintegral_comp_emb MeasurableEquiv.finTwoArrow.symm.measurableEmbedding f).symm
    _ = ∫⁻ z : ℝ × ℝ, f ![z.1, z.2] := by rw [he]; rfl
    _ = _ := lintegral_prod _ hmeas.aemeasurable

/-- Coordinate Tonelli formula with the second coordinate integrated outside. -/
theorem lintegral_two_coordinates_symm {f : (Fin 2 → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x) = ∫⁻ v : ℝ, ∫⁻ u : ℝ, f ![u, v] := by
  have hmeas : Measurable (fun z : ℝ × ℝ => f ![z.1, z.2]) := hf.comp (by fun_prop)
  rw [lintegral_two_coordinates hf]
  exact lintegral_lintegral_swap hmeas.aemeasurable

end WaveTurbulence.Fourier
