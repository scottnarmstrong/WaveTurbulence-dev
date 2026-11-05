/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ZOperations
/-! The exact pointwise remainder decay supplied by the fixedpoint Z radius. -/
public section
namespace WaveTurbulence.Induct
open scoped ENNReal

theorem norm_le_of_ZNorm_le {d p : ℕ} (L Λ : ℝ)
    {b : ZTime p → (Fin d → ℤ) → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hb : ZNorm L Λ b ≤ ENNReal.ofReal r) (t : ZTime p) (n : Fin d → ℤ) :
    ‖b t n‖ ≤ jbr (latticePoint L n) ^ (-Λ) * r := by
  have hw := zWeight_pos L Λ n
  have hbound : zWeight L Λ n * ‖b t n‖ ≤ r :=
    (ENNReal.ofReal_le_ofReal_iff hr).mp
      ((le_iSup_of_le t (le_iSup (fun n => ENNReal.ofReal (zWeight L Λ n * ‖b t n‖)) n)).trans hb)
  have hnorm : ‖b t n‖ ≤ r / zWeight L Λ n :=
    (le_div_iff₀ hw).mpr (by simpa only [mul_comm] using hbound)
  have hj : 0 < jbr (latticePoint L n) := Real.sqrt_pos.mpr (by positivity)
  simpa only [Real.rpow_neg hj.le, div_eq_mul_inv, zWeight, mul_comm] using hnorm

end WaveTurbulence.Induct
