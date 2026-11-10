/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoordinateLinearMap
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
/-! Derivative identities for explicit source approximations follow from their actual
uniform kernel limits. This is a proved calculus lemma, not an additional spine input. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Filter Finset
open scoped Topology

theorem hasFDerivAt_of_uniform_coordinate_limits {I : Type*} {d : ℕ} {l : Filter I} [NeBot l]
    (f : I → Mom d → ℂ) (F : Mom d → ℂ) (D : Fin d → Mom d → ℂ)
    (hf : ∀ᶠ n in l, Differentiable ℝ (f n))
    (hval : ∀ x, Tendsto (fun n => f n x) l (𝓝 (F x)))
    (hder : ∀ j, TendstoUniformly (fun n x => partialMom j (f n) x) (D j) l)
    (x : Mom d) : HasFDerivAt F (coordinateLinearMap (fun j => D j x)) x := by
  have hD : TendstoUniformly (fun n x => fderiv ℝ (f n) x)
      (fun x => coordinateLinearMap (fun j => D j x)) l := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    have hden : 0 < (d : ℝ) + 1 := by positivity
    have hε' : 0 < ε / ((d : ℝ) + 1) := div_pos hε hden
    have hj (j : Fin d) : ∀ᶠ n in l, ∀ y,
        ‖partialMom j (f n) y - D j y‖ < ε / ((d : ℝ) + 1) := by
      have hh := Metric.tendstoUniformly_iff.mp (hder j) _ hε'
      filter_upwards [hh] with n hn
      intro y
      rw [← dist_eq_norm, dist_comm]
      exact hn y
    have hall : ∀ᶠ n in l, ∀ j : Fin d, ∀ y,
        ‖partialMom j (f n) y - D j y‖ < ε / ((d : ℝ) + 1) := eventually_all.mpr hj
    filter_upwards [hall] with n hn
    intro y
    rw [dist_comm, dist_eq_norm]
    apply (norm_fderiv_sub_coordinateLinearMap_le (f n) (fun j => D j y) y).trans_lt
    calc
      _ ≤ ∑ _j : Fin d, ε / ((d : ℝ) + 1) := sum_le_sum (fun j _ => (hn j y).le)
      _ = (d : ℝ) * (ε / ((d : ℝ) + 1)) := by simp
      _ < ε := by
        rw [← mul_div_assoc]
        apply (div_lt_iff₀ hden).mpr
        nlinarith
  apply hasFDerivAt_of_tendstoUniformlyOnFilter
    (hD.tendstoUniformlyOnFilter.mono_right le_top)
  · exact eventually_prod_iff.mpr ⟨(fun n => Differentiable ℝ (f n)), hf,
      (fun _ => True), Filter.Eventually.of_forall (fun _ => trivial),
      fun {n} hn {y} _ => (hn y).hasFDerivAt⟩
  · exact Filter.Eventually.of_forall hval

end WaveTurbulence.LGSpine
