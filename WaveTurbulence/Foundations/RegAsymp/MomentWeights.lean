/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.ClassJR.MCSRep
public import WaveTurbulence.Foundations.ApproxNT.AppTools

/-! # Comparing the NT maximum moment with the J3 per-variable moments -/

public section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR Finset
open scoped ENNReal

/-- The Japanese bracket is bounded by1+absolute value. -/
private theorem sqrt_one_add_sq_le (x : ℝ) : Real.sqrt (1+x^2) ≤ 1+|x| := by
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · nlinarith only [sq_abs x,abs_nonneg x]

/-- Maximum coordinate weight is bounded by the sum of the author's weights,
including the empty-variable case. -/
theorem wmax_le_sum_abs {ι : Type} [Fintype ι] {b : ℝ} (hb : 0 ≤ b) (α : ι → ℝ) :
    ApproxNT.wmax b α ≤ ∑ i, (1+|α i|) ^ b := by
  classical
  rcases isEmpty_or_nonempty ι with hi | hi
  · simp [ApproxNT.wmax]
  · unfold ApproxNT.wmax
    apply ciSup_le
    intro i
    exact (Real.rpow_le_rpow (Real.sqrt_nonneg _) (sqrt_one_add_sq_le _) hb).trans
      (single_le_sum (f := fun j => (1+|α j|)^b)
        (fun j _ => Real.rpow_nonneg (by positivity) b) (mem_univ i))

theorem ofReal_wmax_le_sum {ι : Type} [Fintype ι] {b : ℝ} (hb : 0 ≤ b) (α : ι → ℝ) :
    ENNReal.ofReal (ApproxNT.wmax b α) ≤ ∑ i, (1+‖α i‖ₑ)^b := by
  have he (x : ℝ) : (1+‖x‖ₑ)^b = ENNReal.ofReal ((1+|x|)^b) := by
    rw [one_add_enorm_eq,← ENNReal.ofReal_rpow_of_pos (by positivity : 0 < 1+|x|)]
  simp_rw [he]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  exact ENNReal.ofReal_le_ofReal (wmax_le_sum_abs hb α)

end WaveTurbulence.RegAsymp
