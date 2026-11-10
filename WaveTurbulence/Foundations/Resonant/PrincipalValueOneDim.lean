/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral

/-!
# One-dimensional principal-value cancellation

The scalar cancellation used in DH21 Lemma 6.3 (L1338–L1347): an even cutoff
allows replacement of `f(u)/u` by `(f(u)-f(-u))/(2u)`. The latter has a
continuous extension at zero and is integrable for a compactly supported test
function differentiable at zero. These are analytic helpers, not the
frequency-uniform estimate of Lemma 6.3.
-/

public section

open MeasureTheory Filter Topology Set

namespace WaveTurbulence.Resonant

/-- A scalar cutoff equal to one near zero. Smooth cutoffs of DH21 §2 satisfy
these hypotheses; differentiability of the cutoff is unnecessary here. -/
structure IsPVCutoff (χ : ℝ → ℝ) : Prop where
  cont : Continuous χ
  compact : HasCompactSupport χ
  even : ∀ u, χ (-u) = χ u
  near : χ =ᶠ[𝓝 0] fun _ => 1

/-- Finite truncation by `χ∞(μu) = 1 - χ(μu)`. -/
@[expose] noncomputable def pvTruncation (χ : ℝ → ℝ) (μ : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ u, ((1 - χ (μ * u)) / u) * f u

/-- The continuous symmetric quotient, with its derivative value at zero. -/
@[expose] noncomputable def pvQuotient (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  2⁻¹ * dslope (fun v => f v - f (-v)) 0 u

theorem pvQuotient_of_ne (f : ℝ → ℝ) {u : ℝ} (hu : u ≠ 0) :
    pvQuotient f u = (f u - f (-u)) / (2 * u) := by
  simp [pvQuotient, dslope_of_ne _ hu, slope_def_field]
  ring

namespace IsPVCutoff

variable {χ : ℝ → ℝ}

theorem continuous_div (hχ : IsPVCutoff χ) (μ : ℝ) :
    Continuous (fun u : ℝ => (1 - χ (μ * u)) / u) := by
  rw [continuous_iff_continuousAt]
  intro u
  by_cases hu : u = 0
  · subst u
    have ht : Tendsto (fun u : ℝ => μ * u) (𝓝 0) (𝓝 0) := by
      exact tendsto_const_nhds.mul tendsto_id |>.trans
        (by simp)
    have he : (fun u : ℝ => (1 - χ (μ * u)) / u) =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [ht.eventually hχ.near] with u hu
      simp only [hu, sub_self, zero_div]
    exact continuousAt_const.congr he.symm
  · exact (continuous_const.sub (hχ.cont.comp
      (continuous_const.mul continuous_id))).continuousAt.div continuousAt_id hu

/-- The cutoff disappears at every nonzero point as its scale tends to infinity. -/
theorem eventually_comp_eq_zero (hχ : IsPVCutoff χ) {u : ℝ} (hu : u ≠ 0) :
    (fun μ : ℝ => χ (μ * u)) =ᶠ[atTop] fun _ => 0 := by
  have he := hasCompactSupport_iff_eventuallyEq.mp hχ.compact
  rw [Filter.coclosedCompact_eq_cocompact] at he
  exact (Filter.tendsto_cocompact_mul_right₀ hu).comp
    (tendsto_id.mono_right atTop_le_cocompact) |>.eventually he

end IsPVCutoff

end WaveTurbulence.Resonant
