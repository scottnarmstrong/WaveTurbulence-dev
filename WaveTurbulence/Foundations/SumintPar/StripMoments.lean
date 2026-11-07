/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.StripIntegral

/-!
# Turning strip widths into first moments

The ordering strip has radius `|s|/c`; its exact mass supplies one extra
factor `c⁻¹` before the inner time rescaling is counted.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.SumintPar

/-- A strip of radius `|s|/c` has exactly the rescaled first-moment mass. -/
theorem lintegral_first_moment_strip (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    {c : ℝ} (hc : 0 < c) (e : ℝ) :
    (∫⁻ t : ℝ, ∫⁻ s : ℝ, if |t-e| ≤ |s|/c then f s else 0) =
      ENNReal.ofReal (2/c) * ∫⁻ s : ℝ, ENNReal.ofReal |s| * f s := by
  have hR : Measurable (fun s : ℝ => |s|/c) :=
    continuous_abs.measurable.div_const c
  rw [lintegral_time_strip f hf _ hR e]
  have he (s : ℝ) : 2*(|s|/c) = (2/c)*|s| := by ring
  have hp : 0 ≤ (2:ℝ)/c := div_nonneg (by norm_num) hc.le
  simp_rw [he, ENNReal.ofReal_mul hp]
  have hm : Measurable (fun s : ℝ => ENNReal.ofReal |s| * f s) :=
    (ENNReal.measurable_ofReal.comp continuous_abs.measurable).mul hf
  calc
    _ = ∫⁻ s : ℝ, ENNReal.ofReal (2/c) * (ENNReal.ofReal |s| * f s) := by
      apply lintegral_congr
      intro s
      ac_rfl
    _ = _ := lintegral_const_mul _ hm

/-- Enlarging an ordering strip by `h` costs its ordinary mass plus its
rescaled first moment. This is the pair incoherence strip. -/
theorem lintegral_offset_first_moment_strip (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    {c h : ℝ} (hc : 0 < c) (hh : 0 ≤ h) (e : ℝ) :
    (∫⁻ t : ℝ, ∫⁻ s : ℝ, if |t-e| ≤ h+|s|/c then f s else 0) =
      ENNReal.ofReal (2*h) * (∫⁻ s : ℝ, f s) +
        ENNReal.ofReal (2/c) * ∫⁻ s : ℝ, ENNReal.ofReal |s| * f s := by
  have hR : Measurable (fun s : ℝ => h+|s|/c) :=
    measurable_const.add (continuous_abs.measurable.div_const c)
  rw [lintegral_time_strip f hf _ hR e]
  have hp : 0 ≤ (2:ℝ)/c := div_nonneg (by norm_num) hc.le
  have hw (s : ℝ) : ENNReal.ofReal (2*(h+|s|/c)) =
      ENNReal.ofReal (2*h)+ENNReal.ofReal (2/c)*ENNReal.ofReal |s| := by
    rw [← ENNReal.ofReal_mul hp, ← ENNReal.ofReal_add (mul_nonneg (by norm_num) hh)
      (mul_nonneg hp (abs_nonneg s))]
    congr 1
    ring
  simp_rw [hw]
  have he (s : ℝ) : f s*(ENNReal.ofReal (2*h)+ENNReal.ofReal (2/c)*ENNReal.ofReal |s|) =
      ENNReal.ofReal (2*h)*f s+ENNReal.ofReal (2/c)*(ENNReal.ofReal |s| * f s) := by ring
  simp_rw [he]
  rw [lintegral_add_left (show Measurable (fun s : ℝ => ENNReal.ofReal (2*h)*f s) from measurable_const.mul hf), lintegral_const_mul _ hf,
    lintegral_const_mul _ (show Measurable (fun s : ℝ => ENNReal.ofReal |s| * f s) from
      (ENNReal.measurable_ofReal.comp continuous_abs.measurable).mul hf)]

end WaveTurbulence.SumintPar
