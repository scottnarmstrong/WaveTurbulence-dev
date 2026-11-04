/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.LocalizedKernelOperator
public import WaveTurbulence.Foundations.Fourier.TimeFourierLimit
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Smooth approximation for localized time kernel operators

Approximation takes place in the input `Lᵖ` space. Cutoff localization
and the bounded kernel then give physical `L¹` output convergence, hence
pointwise Fourier convergence. No regularity of the input representative
is required.
-/

public section

open MeasureTheory Filter
open scoped ContDiff ENNReal Topology

namespace WaveTurbulence.Fourier

/-- A fixed positive error sequence tending to zero. -/
@[expose] noncomputable def smoothApproximationError (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / ((n : ℝ) + 1))

/-- The error sequence tends to zero in the extended nonnegative reals. -/
theorem tendsto_smoothApproximationError :
    Tendsto smoothApproximationError atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0)
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using h

/-- A finite-norm input admits smooth compact approximants with convergent literal output transforms. -/
theorem exists_localizedKernel_smooth_approximation {p : ℝ} (hp : 1 ≤ p)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (h : CutoffControl χ)
    {K : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℂ}
    (hK : Measurable (fun z : (Fin 2 → ℝ) × (Fin 2 → ℝ) => K z.1 z.2))
    (hKn : ∀ t v, ‖K t v‖ ≤ 1) {F : (Fin 2 → ℝ) → ℂ}
    (hF : MemLp F (ENNReal.ofReal p)) :
    ∃ g : ℕ → (Fin 2 → ℝ) → ℂ,
      (∀ n, ContDiff ℝ ∞ (g n)) ∧ (∀ n, HasCompactSupport (g n)) ∧
      (∀ n, eLpNorm (g n) (ENNReal.ofReal p) ≤
        eLpNorm F (ENNReal.ofReal p) + smoothApproximationError n) ∧
      (∀ ξ, Tendsto (fun n => timeFourier (localizedKernelOperator χ K (g n)) ξ) atTop
        (𝓝 (timeFourier (localizedKernelOperator χ K F) ξ))) := by
  have hp1 : 1 ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have ha (n : ℕ) : ∃ g : (Fin 2 → ℝ) → ℂ, HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
      eLpNorm (F - g) (ENNReal.ofReal p) ≤ smoothApproximationError n :=
    hF.exist_eLpNorm_sub_le ENNReal.ofReal_ne_top hp1 (by positivity : 0 < 1 / ((n : ℝ) + 1))
  choose g hgc hgs hge using ha
  have hgm (n : ℕ) : MemLp (g n) (ENNReal.ofReal p) :=
    (hgs n).continuous.memLp_of_hasCompactSupport (hgc n)
  have hnorm (n : ℕ) : eLpNorm (g n) (ENNReal.ofReal p) ≤
      eLpNorm F (ENNReal.ofReal p) + smoothApproximationError n := by
    have ht : eLpNorm (g n) (ENNReal.ofReal p) ≤ eLpNorm F (ENNReal.ofReal p) +
        eLpNorm (F - g n) (ENNReal.ofReal p) := by
      have hh := eLpNorm_sub_le (f := F) (g := F - g n) (μ := volume) hp1
      simpa only [sub_sub_cancel] using hh
    exact ht.trans (add_le_add le_rfl (hge n))
  have hin : Tendsto (fun n => eLpNorm (fun t => g n t - F t) (ENNReal.ofReal p)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds tendsto_smoothApproximationError
      (fun _ => bot_le)
    intro n
    change eLpNorm (g n - F) (ENNReal.ofReal p) ≤ _
    rw [eLpNorm_sub_comm]
    exact hge n
  let L := cutoffKernelL1Factor h.radius h.bound * localTimeL1Factor p h.radius h.bound
  have hL : L ≠ ⊤ := ENNReal.mul_ne_top (cutoffKernelL1Factor_ne_top _ _)
    (localTimeL1Factor_ne_top hp _ _)
  have hout : Tendsto (fun n => eLpNorm (fun t => localizedKernelOperator χ K (g n) t -
      localizedKernelOperator χ K F t) 1) atTop (𝓝 0) := by
    have hupper : Tendsto (fun n => L * eLpNorm (fun t => g n t - F t) (ENNReal.ofReal p))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul hin (Or.inr hL)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun _ => bot_le) (fun n => eLpNorm_localizedKernelOperator_sub_one_le hp hχ h hK hKn (hgm n) hF)
  refine ⟨g, hgs, hgc, hnorm, ?_⟩
  exact tendsto_timeFourier_of_eLpNorm_sub
    (localizedKernelOperator_integrable hp hχ h hK hKn hF)
    (fun n => localizedKernelOperator_integrable hp hχ h hK hKn (hgm n)) hout

end WaveTurbulence.Fourier
