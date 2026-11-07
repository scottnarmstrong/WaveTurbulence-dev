/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! # Exact finite phase recentering (TARGET vineest Step 1, defKtilde) -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed

/-- Recenter every oscillatory factor at the same exterior clock. The total
phase is computed from the actual factors, so no phase identity is assumed. -/
theorem phase_recenter {ι : Type*} (S : Finset ι) (a τ : ι → ℂ) (t : ℂ) :
    Complex.exp (-t * ∑ i ∈ S, a i) * (∏ i ∈ S, Complex.exp (a i * τ i)) =
      ∏ i ∈ S, Complex.exp (a i * (τ i - t)) := by
  rw [← Complex.exp_sum,← Complex.exp_sum,← Complex.exp_add]
  congr 1
  simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul]
  ring

/-- The exact real resonance convention of TARGET, with its common imaginary
coefficient and no sign absorbed into a redefined resonance. -/
theorem resonance_phase_recenter {ι : Type*} (S : Finset ι) (a τ : ι → ℝ) (c t : ℝ) :
    Complex.exp (((-c * t * ∑ i ∈ S, a i : ℝ) : ℂ) * Complex.I) *
        (∏ i ∈ S, Complex.exp (((c * a i * τ i : ℝ) : ℂ) * Complex.I)) =
      ∏ i ∈ S, Complex.exp (((c * a i * (τ i - t) : ℝ) : ℂ) * Complex.I) := by
  have h := phase_recenter S (fun i => ((c*a i : ℝ) : ℂ)*Complex.I)
    (fun i => (τ i : ℂ)) (t : ℂ)
  have hsum : (∑ i ∈ S, ((c*a i : ℝ) : ℂ)*Complex.I) =
      ((c * ∑ i ∈ S, a i : ℝ) : ℂ)*Complex.I := by
    simp only [← Finset.sum_mul,← Complex.ofReal_sum,← Finset.mul_sum,Complex.ofReal_mul]
  rw [hsum] at h
  have hc : -(t : ℂ) * (((c * ∑ i ∈ S, a i : ℝ) : ℂ)*Complex.I) =
      (((-c*t*∑ i ∈ S, a i : ℝ) : ℂ)*Complex.I) := by push_cast; ring
  have hp (u : ι → ℝ) : (∏ i ∈ S, Complex.exp (((c*a i : ℝ) : ℂ)*Complex.I*(u i : ℂ))) =
      ∏ i ∈ S, Complex.exp (((c*a i*u i : ℝ) : ℂ)*Complex.I) := by
    apply Finset.prod_congr rfl
    intro i _
    congr 1
    push_cast
    ring
  rw [hc,hp] at h
  apply h.trans
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  push_cast
  ring


end WaveTurbulence.RegRed
