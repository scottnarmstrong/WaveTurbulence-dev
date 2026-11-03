/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Simultaneous simple approximation in `L¹` and `Lᵖ`

A single sequence of simple functions approximates an integrable `Lᵖ`
function in both norms. This is the density input for the integral-form
Hausdorff–Young estimate, including functions on an infinite-measure space.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace WaveTurbulence.Fourier

/-- Simultaneous `L¹` and `Lᵖ` approximation by one sequence of simple functions. -/
theorem exists_simpleFunc_L1_Lp_approx {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {f : α → ℂ}
    (hf1 : MemLp f 1 μ) (hfp : MemLp f p μ) :
    ∃ (F : ℕ → SimpleFunc α ℂ) (hF1 : ∀ n, MemLp (F n) 1 μ) (hFp : ∀ n, MemLp (F n) p μ),
      Tendsto (fun n => (hF1 n).toLp (F n)) atTop (𝓝 (hf1.toLp f)) ∧
        Tendsto (fun n => (hFp n).toLp (F n)) atTop (𝓝 (hfp.toLp f)) := by
  let f' := hf1.aestronglyMeasurable.mk f
  have he : f =ᵐ[μ] f' := hf1.aestronglyMeasurable.ae_eq_mk
  have hm : Measurable f' := hf1.aestronglyMeasurable.measurable_mk
  have hf1' : MemLp f' 1 μ := hf1.ae_eq he
  have hfp' : MemLp f' p μ := hfp.ae_eq he
  let F := SimpleFunc.approxOn f' hm (Set.range f' ∪ {0}) 0 (by simp)
  have hF1 (n : ℕ) : MemLp (F n) 1 μ := SimpleFunc.memLp_approxOn_range hm hf1' n
  have hFp (n : ℕ) : MemLp (F n) p μ := SimpleFunc.memLp_approxOn_range hm hfp' n
  refine ⟨F, hF1, hFp, ?_, ?_⟩
  · have h := SimpleFunc.tendsto_approxOn_range_Lp (p := 1) (by simp) hm hf1'
    rw [← MemLp.toLp_congr hf1 hf1' he] at h
    exact h
  · have h := SimpleFunc.tendsto_approxOn_range_Lp hp hm hfp'
    rw [← MemLp.toLp_congr hfp hfp' he] at h
    exact h

end WaveTurbulence.Fourier
