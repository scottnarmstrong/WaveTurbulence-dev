/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.ParameterIteratedDerivative
public import WaveTurbulence.Foundations.Incoh.MomentumModulation
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Parameter continuity of actual derivatives of smooth modulated amplitudes -/

public section
noncomputable section
open scoped ContDiff

namespace WaveTurbulence.Incoh

/-- Actual momentum derivatives vary continuously with the spectral coefficient and frequency,
for any fixed smooth spatial multiplier. -/
theorem continuous_iteratedFDeriv_smooth_modulated {d : ℕ} {X : Type*} [TopologicalSpace X]
    (ψ : Mom d → ℂ) (hψ : ContDiff ℝ ∞ ψ) (c : X → ℂ) (hc : Continuous c)
    (v : X → Mom d) (hv : Continuous v) (k : Mom d) (j : ℕ) :
    Continuous (fun x => iteratedFDeriv ℝ j
      (fun k : Mom d => ψ k * (c x * (Real.fourierChar (inner ℝ (v x) k) : ℂ))) k) := by
  let g := fun v k : Mom d => ψ k * (Real.fourierChar (inner ℝ v k) : ℂ)
  have hg : ContDiff ℝ ∞ (Function.uncurry g) := by
    have hp : ContDiff ℝ ∞ (fun p : Mom d × Mom d => (Real.fourierChar (inner ℝ p.1 p.2) : ℂ)) := by
      simp_rw [Real.fourierChar_apply]
      have hr : ContDiff ℝ ∞ (fun p : Mom d × Mom d => 2 * Real.pi * inner ℝ p.1 p.2) :=
        contDiff_const.mul (contDiff_fst.inner ℝ contDiff_snd)
      have hh : ContDiff ℝ ∞ (fun p : Mom d × Mom d => ((2 * Real.pi * inner ℝ p.1 p.2 : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp hr
      exact (hh.mul contDiff_const).cexp
    exact (hψ.comp contDiff_snd).mul hp
  have hD := (contDiff_parameter_iteratedFDeriv g hg j).continuous
  have hgj (w : Mom d) : ContDiff ℝ ∞ (g w) :=
    hg.comp (f := fun y : Mom d => (w, y)) (contDiff_const.prodMk contDiff_id)
  have he (x : X) : (fun k : Mom d => ψ k * (c x * (Real.fourierChar (inner ℝ (v x) k) : ℂ))) =
      fun k => c x • g (v x) k := by
    funext k
    simp only [g, smul_eq_mul]
    ring
  have hder (x : X) : iteratedFDeriv ℝ j
      (fun k : Mom d => ψ k * (c x * (Real.fourierChar (inner ℝ (v x) k) : ℂ))) k =
        c x • iteratedFDeriv ℝ j (g (v x)) k := by
    rw [he]
    exact iteratedFDeriv_const_smul_apply' ((hgj _).of_le (show (j : ℕ∞ω) ≤ ∞ by simp)).contDiffAt
  simp_rw [hder]
  have hpartial : Continuous (fun x : X => iteratedFDeriv ℝ j (g (v x)) k) :=
    hD.comp (f := fun x : X => (v x, k)) (hv.prodMk continuous_const)
  exact hc.smul hpartial

end WaveTurbulence.Incoh
