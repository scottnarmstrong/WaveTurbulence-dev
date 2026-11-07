/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fin.VecNotation

/-!
# The source output-time shear

The rectangular extension uses differences from the first output time.
Both maps below are literal linear shears with inverse formulas.
-/

@[expose] public section
set_option autoImplicit false
open Set
namespace WaveTurbulence.SumintPar

/-- Original output times expressed in rectangular kernel coordinates. -/
@[expose] def sourceTimeShear (t : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![t 0, t 1-t 0, t 2-t 0]

/-- Rectangular coordinates expressed as the original three output times. -/
@[expose] def sourceTimeUnshear (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![z 0, z 1+z 0, z 2+z 0]

@[simp] theorem sourceTimeShear_unshear (z : Fin 3 → ℝ) :
    sourceTimeShear (sourceTimeUnshear z) = z := by
  ext j
  fin_cases j <;> simp [sourceTimeShear, sourceTimeUnshear]

@[simp] theorem sourceTimeUnshear_shear (t : Fin 3 → ℝ) :
    sourceTimeUnshear (sourceTimeShear t) = t := by
  ext j
  fin_cases j <;> simp [sourceTimeShear, sourceTimeUnshear]

/-- On the actual source cube the sheared coordinates remain in the symmetric cube. -/
theorem abs_sourceTimeShear_le {N : ℝ} (t : Fin 3 → ℝ)
    (ht : ∀ j, t j ∈ Icc 0 N) (j : Fin 3) : |sourceTimeShear t j| ≤ N := by
  fin_cases j
  · simpa [sourceTimeShear, abs_of_nonneg (ht 0).1] using (ht 0).2
  · change |t 1-t 0| ≤ N
    exact abs_le.mpr ⟨by linarith [(ht 1).1, (ht 0).2], by linarith [(ht 1).2, (ht 0).1]⟩
  · change |t 2-t 0| ≤ N
    exact abs_le.mpr ⟨by linarith [(ht 2).1, (ht 0).2], by linarith [(ht 2).2, (ht 0).1]⟩

end WaveTurbulence.SumintPar
