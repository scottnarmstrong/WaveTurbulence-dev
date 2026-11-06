/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafwisePointwise
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
/-! Uniform limits from the literal source error estimate. No new analytic input is introduced. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Filter
open scoped Topology ENNReal

theorem tendstoUniformly_of_enorm_error {I X : Type*} {l : Filter I}
    (f : I → X → ℂ) (F : X → ℂ) (b : I → ℝ)
    (hb : Tendsto b l (𝓝 0))
    (h : ∀ᶠ i in l, ∀ x, ‖f i x - F x‖ₑ ≤ ENNReal.ofReal (b i)) :
    TendstoUniformly f F l := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hsmall : ∀ᶠ i in l, b i < ε := hb.eventually (gt_mem_nhds hε)
  filter_upwards [h, hsmall] with i hi hbi
  intro x
  have hh : ‖f i x - F x‖ < ε := by
    have hh := (hi x).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hε).mpr hbi)
    rw [← ofReal_norm] at hh
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mp hh
  simpa only [dist_eq_norm, norm_sub_rev] using hh

theorem tendsto_reg_error {I : Type*} {l : Filter I} (L : I → ℝ)
    (hL : Tendsto L l atTop) (C δ a B : ℝ) (ha : 0 < a) (n : ℕ) :
    Tendsto (fun i => C * (C * δ) ^ n * L i ^ (-a) * B) l (𝓝 0) := by
  have h := ((tendsto_rpow_neg_atTop ha).comp hL).const_mul (C * (C * δ) ^ n)
  simpa only [mul_zero, zero_mul, Function.comp_def] using h.mul_const B

end WaveTurbulence.LGSpine
