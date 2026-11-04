/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.FixedCoordinateMeasure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Bounded affected factors under fixed/free coordinate integration

A factor supported on its local time box and bounded there by K has
mass at most K times 3 to its arity. This is the elementary time-volume
cost used only for cores touched by the selected endpoint coordinates.
-/

public section

open MeasureTheory Set ENNReal
open scoped Classical

namespace WaveTurbulence.Sumint

/-- Bounded local factors cost at most three to their arity under the mixed fixed/free measure. -/
theorem lintegral_fixedCoordinate_box_le {ι κ : Type*} [Fintype κ]
    (s : Set ι) (x : ι → ℝ) (v : κ → ι) (lo hi : κ → ℝ) (hlen : ∀ j, hi j-lo j ≤ 3)
    (f : (κ → ℝ) → ℝ≥0∞) (K : ℝ≥0∞)
    (hbound : ∀ z ∈ Set.pi Set.univ (fun j => Icc (lo j) (hi j)), f z ≤ K)
    (hzero : ∀ z ∉ Set.pi Set.univ (fun j => Icc (lo j) (hi j)), f z = 0) :
    (∫⁻ z, f z ∂Measure.pi (fun j => fixedCoordinateMeasure s x (v j))) ≤
      K*ENNReal.ofReal (3^(Fintype.card κ):ℝ) := by
  let B := Set.pi Set.univ (fun j => Icc (lo j) (hi j))
  have hB : MeasurableSet B := MeasurableSet.pi (Set.to_countable Set.univ) (fun _ _ => measurableSet_Icc)
  have hf (z : κ → ℝ) : f z ≤ B.indicator (fun _ => K) z := by
    by_cases hz : z ∈ B
    · rw [Set.indicator_of_mem hz]
      exact hbound z hz
    · rw [Set.indicator_of_notMem hz,hzero z hz]
  calc
    _ ≤ ∫⁻ z, B.indicator (fun _ => K) z ∂Measure.pi (fun j => fixedCoordinateMeasure s x (v j)) :=
      lintegral_mono hf
    _ = K*(Measure.pi (fun j => fixedCoordinateMeasure s x (v j))) B := lintegral_indicator_const hB K
    _ ≤ _ := mul_le_mul' le_rfl (fixedCoordinateMeasure_pi_box_le s x v lo hi hlen)

end WaveTurbulence.Sumint
