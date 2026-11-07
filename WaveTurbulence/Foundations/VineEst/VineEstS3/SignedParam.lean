/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.SumintSigned

/-! # The parameters of `signedPhase` are a unimodular product factor (engine step MOD)

`signedPhase` of the datum with parameters `p + Δ` is `signedPhase` of the datum with parameters `p` times
`∏_v e^{πi Δ_v τ_v}`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3.Eng
open WaveTurbulence WaveTurbulence.VineEstS2 Finset
open scoped ENNReal

/-- The unimodular factor `∏_v e^{πi Δ_v τ_v}`. -/
noncomputable def paramFactor {d : ℕ} (D : SumintDatum d) (Δ : D.S.TVar → ℝ) (τ : D.S.TVar → ℝ) : ℂ :=
  ∏ v, Complex.exp ((Real.pi * (Δ v * τ v) : ℝ) * Complex.I)

theorem signedPhase_param {d : ℕ} (D : SumintDatum d) (Δ : D.S.TVar → ℝ)
    (coreFirstSign coreSign : Fin D.S.I → ℤˣ) (L γ δ η : ℝ) (x : D.S.VIdx → (Fin d → ℤ)) (r : Mom d)
    (t : ℝ) (τ : D.S.TVar → ℝ) :
    signedPhase { D with param := fun v => D.param v + Δ v } coreFirstSign coreSign L γ δ η x r t τ =
      signedPhase D coreFirstSign coreSign L γ δ η x r t τ * paramFactor D Δ τ := by
  unfold signedPhase paramFactor
  simp only [Fintype.prod_sum_type, Fintype.prod_sigma]
  simp only [mul_add, add_mul, Complex.ofReal_add, Complex.exp_add, Finset.prod_mul_distrib]
  ring

end WaveTurbulence.VineEstS3.Eng
