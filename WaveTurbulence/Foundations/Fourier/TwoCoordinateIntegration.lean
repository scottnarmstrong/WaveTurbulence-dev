/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
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

/-- Tonelli on a fixed two-coordinate box, with the product restricted measure. -/
theorem lintegral_two_coordinates_box {f : (Fin 2 → ℝ) → ℝ≥0∞} (hf : Measurable f) (R : ℝ) :
    (∫⁻ x in Set.Icc (fun _ : Fin 2 => -R) (fun _ => R), f x) =
      ∫⁻ u in Set.Icc (-R) R, ∫⁻ v in Set.Icc (-R) R, f ![u, v] := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (-R) R)
  have hμ : (volume : Measure (Fin 2 → ℝ)).restrict
      (Set.Icc (fun _ : Fin 2 => -R) (fun _ => R)) = Measure.pi (fun _ : Fin 2 => μ) := by
    rw [← Set.pi_univ_Icc, volume_pi, Measure.restrict_pi_pi]
  have hm := measurePreserving_finTwoArrow μ
  rw [hμ]
  calc
    _ = ∫⁻ z : ℝ × ℝ, f (MeasurableEquiv.finTwoArrow.symm z) ∂μ.prod μ :=
      (hm.symm.lintegral_comp_emb MeasurableEquiv.finTwoArrow.symm.measurableEmbedding f).symm
    _ = ∫⁻ z : ℝ × ℝ, f ![z.1, z.2] ∂μ.prod μ := by
      apply lintegral_congr
      intro z
      congr 1
    _ = _ := lintegral_prod _ (hf.comp (by fun_prop)).aemeasurable

end WaveTurbulence.Fourier
