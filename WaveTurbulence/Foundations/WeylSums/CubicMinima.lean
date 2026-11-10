/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

/-!
# Minimum estimates for the cubic minor-arc reduction

TARGET `lemcubic`, the phase `t⟨x,y⟩+s⟨x,z⟩`. Summing either free
variable first gives two bilinear estimates. Their minimum is separated
into a nonzero-arc product and a zero-arc product by the inequalities here.
-/

public section
namespace WaveTurbulence.WeylSums

theorem min_add_le_add_min {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    min u (v+w) ≤ min u v + min u w := by
  by_cases huv : u ≤ v
  · rw [min_eq_left huv]
    exact (min_le_left _ _).trans (le_add_of_nonneg_right (le_min hu hw))
  · by_cases huw : u ≤ w
    · rw [min_eq_left huw]
      exact (min_le_left _ _).trans (le_add_of_nonneg_left (le_min hu hv))
    · rw [min_eq_right (le_of_not_ge huv), min_eq_right (le_of_not_ge huw)]
      exact min_le_right _ _

/-- The product exponents can be asymmetric; this is used to integrate the
zero rational arc separately from the nonzero numerator contribution. -/
theorem min_rpow_le_rpow_mul {u v d a : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (ha : 0 < a) (had : a < d) :
    min (u^d) (v^d) ≤ u^a * v^(d-a) := by
  have hd : 0 < d := ha.trans had
  have hda : 0 < d-a := sub_pos.mpr had
  by_cases huz : u = 0
  · apply (min_le_left _ _).trans
    rw [huz, Real.zero_rpow hd.ne']
    positivity
  by_cases hvz : v = 0
  · apply (min_le_right _ _).trans
    rw [hvz, Real.zero_rpow hd.ne']
    positivity
  have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm huz)
  have hvp : 0 < v := lt_of_le_of_ne hv (Ne.symm hvz)
  by_cases huv : u ≤ v
  · calc
      _ ≤ u^d := min_le_left _ _
      _ = u^a*u^(d-a) := by rw [← Real.rpow_add hup]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hu huv hda.le) (Real.rpow_nonneg hu _)
  · calc
      _ ≤ v^d := min_le_right _ _
      _ = v^a*v^(d-a) := by rw [← Real.rpow_add hvp]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hv (le_of_not_ge huv) ha.le) (Real.rpow_nonneg hv _)

end WaveTurbulence.WeylSums
