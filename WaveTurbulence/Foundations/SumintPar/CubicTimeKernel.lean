/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.PairKernels
import Mathlib.Tactic

/-!
# Integrable two-time cubic stationary-phase kernels

The source scale `1+|s|+|t|` dominates the product-space norm. In dimension
three the zeroth moment is integrable. Fractional moments strictly below
one are also integrable and give the incoherence gain.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory

namespace WaveTurbulence.SumintPar

private instance : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
  change ((volume : Measure ℝ).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance

/-- The two-time cubic scale dominates the norm used by the integrable radial majorant. -/
theorem one_add_norm_pair_le_cubicScale (p : ℝ × ℝ) :
    1 + ‖p‖ ≤ 1 + |p.1| + |p.2| := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  have hmax : max |p.1| |p.2| ≤ |p.1| + |p.2| := max_le
    (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
  linarith

/-- Every cubic inverse power greater than two is integrable on the two-time plane. -/
theorem integrable_cubicTimeKernel {p : ℝ} (hp : 2 < p) :
    Integrable (fun st : ℝ × ℝ => (1 + |st.1| + |st.2|)^(-p)) := by
  have hi := integrable_one_add_norm (E := ℝ × ℝ) (μ := volume) (r := p) (by simpa using hp)
  apply hi.mono'
  · apply Continuous.aestronglyMeasurable
    apply Continuous.rpow_const
    · fun_prop
    · intro st
      exact Or.inl (by positivity)
  · apply ae_of_all
    intro st
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < 1+‖st‖)
      (one_add_norm_pair_le_cubicScale st) (by linarith)

/-- In particular the exact integer source denominator is integrable for every `d≥3`. -/
theorem integrable_cubicTimeKernel_nat {d : ℕ} (hd : 3 ≤ d) :
    Integrable (fun st : ℝ × ℝ => 1 / (1+|st.1|+|st.2|)^d) := by
  have hi := integrable_cubicTimeKernel (p := (d : ℝ)) (by exact_mod_cast (show 2 < d by omega))
  apply hi.congr
  filter_upwards [] with st
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1+|st.1|+|st.2|),
    Real.rpow_natCast, one_div]

end WaveTurbulence.SumintPar
