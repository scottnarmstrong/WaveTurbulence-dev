/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.Geometric
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.Inversion

/-!
# Gaussian Fourier representation of a smooth cutoff

Multiplying a compactly supported smooth cutoff by `exp(πx²)` still gives a
Schwartz function. Fourier inversion then writes the original cutoff as a
Gaussian times a superposition of linear phases with an integrable weight.
This transfers a uniform Gaussian quadratic-sum bound without a logarithm.
-/

public section

open MeasureTheory
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff

namespace WaveTurbulence.WeylSums

/-- Remove the Gaussian factor from a compactly supported cutoff. -/
@[expose] noncomputable def degaussianCutoff (χ : ℝ → ℂ) (x : ℝ) : ℂ :=
  χ x * (Real.exp (Real.pi * x ^ 2) : ℂ)

theorem hasCompactSupport_degaussianCutoff {χ : ℝ → ℂ} (hχ : HasCompactSupport χ) :
    HasCompactSupport (degaussianCutoff χ) :=
  hχ.mul_right

theorem contDiff_degaussianCutoff {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (degaussianCutoff χ) := by
  unfold degaussianCutoff
  have hg : ContDiff ℝ ∞ (fun x : ℝ => Real.exp (Real.pi * x ^ 2)) := by fun_prop
  exact hχ.mul (Complex.ofRealCLM.contDiff.comp hg)

/-- Every smooth compactly supported cutoff has a Gaussian Fourier
representation with an integrable complex weight. -/
theorem exists_gaussian_fourier_representation (χ : ℝ → ℂ)
    (hc : HasCompactSupport χ) (hs : ContDiff ℝ ∞ χ) :
    ∃ F : ℝ → ℂ, Integrable F ∧ ∀ x : ℝ,
      χ x = (Real.exp (-Real.pi * x ^ 2) : ℂ) * ∫ ξ : ℝ, F ξ * e (ξ * x) := by
  let ψ : 𝓢(ℝ, ℂ) := (hasCompactSupport_degaussianCutoff hc).toSchwartzMap
    (contDiff_degaussianCutoff hs)
  let F : 𝓢(ℝ, ℂ) := 𝓕 ψ
  refine ⟨(F : ℝ → ℂ), F.integrable, ?_⟩
  intro x
  have hinv := ψ.integrable.fourierInv_fourier_eq (v := x)
    (show Integrable (𝓕 (ψ : ℝ → ℂ)) from F.integrable) ψ.continuous.continuousAt
  have heq : (∫ ξ : ℝ, F ξ * e (ξ * x)) = ψ x := by
    rw [Real.fourierInv_eq'] at hinv
    simpa only [F, SchwartzMap.fourier_coe, Real.inner_apply, e, smul_eq_mul, mul_comm] using hinv
  rw [heq]
  change χ x = (Real.exp (-Real.pi * x ^ 2) : ℂ) *
    (χ x * (Real.exp (Real.pi * x ^ 2) : ℂ))
  have hcancel : (Real.exp (-Real.pi * x ^ 2) : ℂ) *
      (Real.exp (Real.pi * x ^ 2) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add,
      show -Real.pi * x ^ 2 + Real.pi * x ^ 2 = 0 by ring, Real.exp_zero, Complex.ofReal_one]
  calc
    _ = χ x * ((Real.exp (-Real.pi * x ^ 2) : ℂ) * (Real.exp (Real.pi * x ^ 2) : ℂ)) := by
      rw [hcancel, mul_one]
    _ = _ := by ring

end WaveTurbulence.WeylSums
