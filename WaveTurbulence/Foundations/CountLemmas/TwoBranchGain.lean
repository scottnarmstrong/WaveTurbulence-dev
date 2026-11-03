/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Combining the baseline and independent-strip pair bounds -/

public section
namespace WaveTurbulence.CountLemmas

/-- The baseline and P⁻¹ bounds combine without losing a δ-dependent
constant. The gain may be capped by any smaller positive X. -/
theorem two_branch_gain {N A B V τ P X : ℝ} (hN : 0 ≤ N)
    (hτ : 0 < τ) (hP : 0 < P) (hX : 0 < X) (hXle : X ≤ 1+P/τ)
    (hbase : N ≤ A*V) (hstrip : N ≤ B*(τ*V/P)) :
    N ≤ (A+B)*V*X⁻¹ := by
  have hp := mul_le_mul_of_nonneg_right hstrip (div_nonneg hP.le hτ.le)
  have heq : B*(τ*V/P)*(P/τ) = B*V := by field_simp
  rw [heq] at hp
  have hm : N*X ≤ (A+B)*V := by
    calc
      _ ≤ N*(1+P/τ) := mul_le_mul_of_nonneg_left hXle hN
      _ = N+N*(P/τ) := by ring
      _ ≤ A*V+B*V := add_le_add hbase hp
      _ = _ := by ring
  simpa only [div_eq_mul_inv] using (le_div_iff₀ hX).mpr hm

end WaveTurbulence.CountLemmas
