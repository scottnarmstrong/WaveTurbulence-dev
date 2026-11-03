/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TimeInterpolation
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Tactic

/-!
# Fourier limits and Fatou for weighted time norms

Convergence in physical `L¹` gives pointwise Fourier convergence. Fatou
then transfers any uniform weighted Fourier estimate to the limit.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace WaveTurbulence.Fourier

/-- The ordinary time Fourier transform is bounded pointwise by the extended input `L¹` norm. -/
theorem enorm_timeFourier_le_eLpNorm_one {r : ℕ} (f : (Fin r → ℝ) → ℂ) (ξ : Fin r → ℝ) :
    ‖timeFourier f ξ‖ₑ ≤ eLpNorm f 1 := by
  apply le_trans (enorm_integral_le_lintegral_enorm _)
  simpa only [Circle.enorm_smul] using (lintegral_enorm_le_eLpNorm_one (f := f) (μ := volume))

/-- Subtraction commutes with the literal Fourier integral on integrable inputs. -/
theorem timeFourier_sub {r : ℕ} {f g : (Fin r → ℝ) → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    timeFourier (fun t => f t - g t) = fun ξ => timeFourier f ξ - timeFourier g ξ := by
  have hL : Continuous (fun p : (Fin r → ℝ) × (Fin r → ℝ) => timePairing r p.1 p.2) := by
    change Continuous (fun p : (Fin r → ℝ) × (Fin r → ℝ) => ∑ j, p.1 j * p.2 j)
    fun_prop
  funext ξ
  change (∫ t, Real.fourierChar (-timePairing r t ξ) • (f t - g t)) = _
  simp_rw [smul_sub]
  rw [integral_sub
    ((VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar hL ξ).mpr hf)
    ((VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar hL ξ).mpr hg)]
  rfl

/-- The physical `L¹` distance controls Fourier distance at every frequency. -/
theorem edist_timeFourier_le_eLpNorm_sub {r : ℕ} {f g : (Fin r → ℝ) → ℂ}
    (hf : Integrable f) (hg : Integrable g) (ξ : Fin r → ℝ) :
    edist (timeFourier f ξ) (timeFourier g ξ) ≤ eLpNorm (fun t => f t - g t) 1 := by
  rw [edist_eq_enorm_sub, ← congrFun (timeFourier_sub hf hg) ξ]
  exact enorm_timeFourier_le_eLpNorm_one _ _

/-- Physical `L¹` convergence implies pointwise Fourier convergence. -/
theorem tendsto_timeFourier_of_eLpNorm_sub {r : ℕ}
    {f : (Fin r → ℝ) → ℂ} {fₙ : ℕ → (Fin r → ℝ) → ℂ}
    (hf : Integrable f) (hfn : ∀ n, Integrable (fₙ n))
    (hlim : Tendsto (fun n => eLpNorm (fun t => fₙ n t - f t) 1) atTop (𝓝 0))
    (ξ : Fin r → ℝ) : Tendsto (fun n => timeFourier (fₙ n) ξ) atTop (𝓝 (timeFourier f ξ)) := by
  rw [tendsto_iff_edist_tendsto_0]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) (fun n => edist_timeFourier_le_eLpNorm_sub (hfn n) hf ξ)

/-- Fatou transfers weighted time Fourier bounds along pointwise Fourier convergence. -/
theorem timeFourierNorm_le_liminf_of_tendsto {r : ℕ} (θ : ℝ)
    {f : (Fin r → ℝ) → ℂ} {fₙ : ℕ → (Fin r → ℝ) → ℂ}
    (hf : Integrable f) (hfn : ∀ n, Integrable (fₙ n))
    (hlim : ∀ ξ, Tendsto (fun n => timeFourier (fₙ n) ξ) atTop (𝓝 (timeFourier f ξ))) :
    timeFourierNorm θ f ≤ liminf (fun n => timeFourierNorm θ (fₙ n)) atTop := by
  have ht (ξ : Fin r → ℝ) : Tendsto
      (fun n => timeWeight θ ξ * ‖timeFourier (fₙ n) ξ‖ₑ) atTop
      (𝓝 (timeWeight θ ξ * ‖timeFourier f ξ‖ₑ)) := by
    have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((hlim ξ).norm.const_mul (timeBracket ξ ^ θ))
    simpa only [ENNReal.ofReal_mul (Real.rpow_nonneg (timeBracket_pos ξ).le _),
      ofReal_norm, timeWeight, Function.comp_def] using hh
  rw [timeFourierNorm_eq_lintegral hf]
  calc
    _ = ∫⁻ ξ, liminf (fun n => timeWeight θ ξ * ‖timeFourier (fₙ n) ξ‖ₑ) atTop :=
      lintegral_congr (fun ξ => (ht ξ).liminf_eq.symm)
    _ ≤ liminf (fun n => ∫⁻ ξ, timeWeight θ ξ * ‖timeFourier (fₙ n) ξ‖ₑ) atTop :=
      lintegral_liminf_le (fun n => (timeWeight_measurable θ).mul
        (timeFourier_continuous (hfn n)).measurable.enorm)
    _ = _ := by simp_rw [timeFourierNorm_eq_lintegral (hfn _)]

end WaveTurbulence.Fourier
