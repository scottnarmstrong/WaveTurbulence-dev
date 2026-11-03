/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.NonstationaryNegative
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue

/-!
# A uniform second-derivative integral estimate

Split at derivative levels `±t`. The central interval has length at most
`2t/μ`, and the two exterior intervals satisfy first-derivative estimates.
No separation from endpoint frequencies is needed.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- Uniform second-derivative bound with a free positive threshold. -/
theorem norm_integral_expPhase_le_of_second_deriv_pos {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {a b μ t : ℝ} (hab : a ≤ b) (hμ : 0 < μ) (ht : 0 < t)
    (hcurv : ∀ x ∈ Icc a b, μ ≤ deriv (deriv f) x) :
    ‖∫ x in a..b, expPhase (f x)‖ ≤ 2 * t / μ + 2 / (Real.pi * t) := by
  have hf1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hsec := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
    hf1.continuous.continuousOn (hf1.differentiable (by norm_num)).differentiableOn
    (fun x hx => hcurv x (interior_subset hx))
  have hmono : MonotoneOn (deriv f) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hf1.continuous.continuousOn
      (hf1.differentiable (by norm_num)).differentiableOn
    intro x hx
    exact hμ.le.trans (hcurv x (interior_subset hx))
  have hnon : 1 / (Real.pi * t) ≤ 2 * t / μ + 2 / (Real.pi * t) := by
    have h1 : 0 ≤ 2 * t / μ := by positivity
    have h2 : 0 ≤ 1 / (Real.pi * t) := by positivity
    calc
      _ ≤ 2 * t / μ + (1 / (Real.pi * t) + 1 / (Real.pi * t)) := by linarith only [h1, h2]
      _ = _ := by ring
  by_cases hpa : t ≤ deriv f a
  · apply (norm_integral_expPhase_le_of_deriv_pos hf hab ht
      (fun x hx => hpa.trans (hmono (left_mem_Icc.mpr hab) hx hx.1))
      (fun x hx => hμ.le.trans (hcurv x hx))).trans hnon
  by_cases hnb : deriv f b ≤ -t
  · apply (norm_integral_expPhase_le_of_deriv_neg hf hab ht
      (fun x hx => (hmono hx (right_mem_Icc.mpr hab) hx.2).trans hnb)
      (fun x hx => hμ.le.trans (hcurv x hx))).trans hnon
  obtain ⟨l, hl, hfl, hlcase⟩ : ∃ l ∈ Icc a b, -t ≤ deriv f l ∧ (l = a ∨ deriv f l = -t) := by
    by_cases hla : -t ≤ deriv f a
    · exact ⟨a, left_mem_Icc.mpr hab, hla, Or.inl rfl⟩
    · obtain ⟨l, hl, hfl⟩ := intermediate_value_Icc hab hf1.continuous.continuousOn
        (show -t ∈ Icc (deriv f a) (deriv f b) from ⟨(not_le.mp hla).le, (not_le.mp hnb).le⟩)
      exact ⟨l, hl, hfl.symm.le, Or.inr hfl⟩
  obtain ⟨u, hu, hfu, hucase⟩ : ∃ u ∈ Icc a b, deriv f u ≤ t ∧ (u = b ∨ deriv f u = t) := by
    by_cases hub : deriv f b ≤ t
    · exact ⟨b, right_mem_Icc.mpr hab, hub, Or.inl rfl⟩
    · obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc hab hf1.continuous.continuousOn
        (show t ∈ Icc (deriv f a) (deriv f b) from ⟨(not_le.mp hpa).le, (not_le.mp hub).le⟩)
      exact ⟨u, hu, hfu.le, Or.inr hfu⟩
  have hlu : l ≤ u := by
    rcases hlcase with rfl | hlcase
    · exact hu.1
    rcases hucase with rfl | hucase
    · exact hl.2
    by_contra h
    have hh := hmono hu hl (not_le.mp h).le
    rw [hlcase, hucase] at hh
    linarith only [hh, ht]
  have hwidth : u - l ≤ 2 * t / μ := by
    have hh := hsec l hl u hu hlu
    apply (le_div_iff₀ hμ).mpr
    nlinarith only [hh, hfl, hfu]
  have hleft : ‖∫ x in a..l, expPhase (f x)‖ ≤ 1 / (Real.pi * t) := by
    rcases hlcase with rfl | heq
    · simp only [intervalIntegral.integral_same, norm_zero]
      positivity
    · exact norm_integral_expPhase_le_of_deriv_neg hf hl.1 ht
        (fun x hx => (hmono ⟨hx.1, hx.2.trans hl.2⟩ hl hx.2).trans heq.le)
        (fun x hx => hμ.le.trans (hcurv x ⟨hx.1, hx.2.trans hl.2⟩))
  have hright : ‖∫ x in u..b, expPhase (f x)‖ ≤ 1 / (Real.pi * t) := by
    rcases hucase with rfl | heq
    · simp only [intervalIntegral.integral_same, norm_zero]
      positivity
    · exact norm_integral_expPhase_le_of_deriv_pos hf hu.2 ht
        (fun x hx => heq.symm.le.trans (hmono hu ⟨hu.1.trans hx.1, hx.2⟩ hx.1))
        (fun x hx => hμ.le.trans (hcurv x ⟨hu.1.trans hx.1, hx.2⟩))
  have hmiddle := (norm_integral_expPhase_le hlu f).trans hwidth
  have hcf := (contDiff_expPhase 0).continuous.comp hf.continuous
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hcf.intervalIntegrable (μ := volume) a l) (hcf.intervalIntegrable (μ := volume) l u)
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (hcf.intervalIntegrable (μ := volume) a u) (hcf.intervalIntegrable (μ := volume) u b)
  simp only [Function.comp_apply] at h1 h2
  rw [← h2, ← h1]
  calc
    _ ≤ (‖∫ x in a..l, expPhase (f x)‖ + ‖∫ x in l..u, expPhase (f x)‖) +
        ‖∫ x in u..b, expPhase (f x)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (1 / (Real.pi * t) + 2 * t / μ) + 1 / (Real.pi * t) :=
      add_le_add (add_le_add hleft hmiddle) hright
    _ = _ := by ring

end WaveTurbulence.VdCB
