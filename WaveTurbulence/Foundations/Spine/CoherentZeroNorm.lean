/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.ExplicitCoherentZero
public import WaveTurbulence.Foundations.Spine.RemainderInputs
/-! Exact high-order spatial bound for the coherent zero-order remainder. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open scoped ENNReal

theorem four_Lambda_next_le (P : WTParams) (hd : 1 ≤ P.d) {p : ℕ} (hp : p < P.D) :
    4 * P.Lambda (p + 1) ≤ P.Lambda p := by
  have he : P.D + 1 - p = (P.D + 1 - (p + 1)) + 1 := by omega
  unfold WTParams.Lambda
  rw [he, pow_succ]
  exact (Nat.mul_le_mul_right _ (by omega : 4 ≤ 40 * P.d)).trans_eq (Nat.mul_comm _ _)

theorem theta_next_le (P : WTParams) (p : ℕ) : P.theta (p + 1) ≤ P.theta p := by
  unfold WTParams.theta
  rw [pow_succ ((2 : ℝ)⁻¹) p]
  have he : 0 ≤ P.η ^ 20 := by positivity
  have hp : 0 ≤ (2 : ℝ)⁻¹ ^ p := by positivity
  have hh : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
  rw [hh] at hp ⊢
  nlinarith [mul_nonneg he hp]

theorem coherent_zero_SNorm_bound (P : WTParams) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L)
    {p : ℕ} (hp : p < P.D) (R : ℕ → Mom P.d → ℝ) (hR : RemainderBound P R p)
    (t : ℝ) :
    SNorm (4 * P.Lambda (p + 1)) (4 * P.Lambda (p + 1))
      (fun k => coherentCoupleSum P (inputsF P R) (p + 1) 0 t k -
        (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p 0 t k : ℂ)) ≤
      ENNReal.ofReal (P.L ^ (-(4 * P.theta (p + 1) + P.theta p) / 5)) := by
  have he : (fun k => coherentCoupleSum P (inputsF P R) (p + 1) 0 t k -
      (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p 0 t k : ℂ)) = fun k => (R p k : ℂ) :=
    funext (coherentCoupleSum_zero_sub_taylor P R p t)
  rw [he]
  have hbound := hR p le_rfl
  have hΛ := forty_dim_le_Lambda P hd hp.le
  have hc := contDiff_of_SNorm_bound (by omega : P.Lambda p ≠ 0) _ _ hbound
  apply (SNorm_mono_bound (four_Lambda_next_le P hd hp) (four_Lambda_next_le P hd hp)
    _ hc _ (Real.rpow_nonneg (zero_le_one.trans hL) _) hbound).trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow_of_exponent_le hL
  have ht := theta_next_le P p
  linarith

end WaveTurbulence.LGSpine
