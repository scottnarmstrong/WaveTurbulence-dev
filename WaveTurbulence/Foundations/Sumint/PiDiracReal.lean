/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The finite real coordinate product of point masses

Fixing every coordinate is exactly the point mass at the full vector.
The proof checks the native finite product measure on coordinate boxes,
including the empty-index convention.
-/

public section

open MeasureTheory Set
open scoped Classical

namespace WaveTurbulence.Sumint

/-- The finite product of scalar Dirac measures is the Dirac measure at the full coordinate vector. -/
theorem pi_dirac_real_eq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    Measure.pi (fun i => Measure.dirac (x i)) = Measure.dirac x := by
  refine Measure.pi_eq (μ := fun i => Measure.dirac (x i)) (fun s hs => ?_)
  by_cases h : ∀ i, x i ∈ s i
  · have hx : x ∈ Set.pi Set.univ s := fun i _ => h i
    rw [Measure.dirac_apply_of_mem hx]
    have hi (i : ι) : Measure.dirac (x i) (s i) = 1 := Measure.dirac_apply_of_mem (h i)
    simp_rw [hi]
    simp
  · obtain ⟨i,hi⟩ := not_forall.mp h
    have hx : x ∉ Set.pi Set.univ s := fun hx => hi (hx i (Set.mem_univ i))
    rw [Measure.dirac_apply,Set.indicator_of_notMem hx]
    have hcomp : Measure.dirac (x i) (s i) = 0 := by
      rw [Measure.dirac_apply,Set.indicator_of_notMem hi]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) hcomp).symm

end WaveTurbulence.Sumint
