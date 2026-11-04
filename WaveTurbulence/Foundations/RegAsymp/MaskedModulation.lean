/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.MaskedSourceDerivativeBound
public import WaveTurbulence.Foundations.Incoh.SmoothModulatedDerivative

/-! # Spatial derivatives of the actual masked root modulation

The scalar may contain the full NT remainder. Its independence of the
root momentum is the only property used in this derivative estimate.
-/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Incoh
open scoped ContDiff

/-- The literal root dependence of a localized spectral remainder. -/
def maskedModulation {d m : ℕ} (c : Fin m → Fin d → ℤ) (a : ℂ) (v k : Mom d) : ℂ :=
  sourceRootMask c k * (a * (Real.fourierChar (inner ℝ v k) : ℂ))

theorem contDiff_maskedModulation {d m : ℕ} (c : Fin m → Fin d → ℤ) (a : ℂ) (v : Mom d) :
    ContDiff ℝ ∞ (maskedModulation c a v) :=
  (contDiff_sourceRootMask c).mul ((contDiff_momentumModulation v).const_smul a)

/-- All lower modulation derivatives share one fixed moment order. -/
theorem norm_iteratedFDeriv_scalar_modulation_le {d J j : ℕ} (a : ℂ) (v k : Mom d) (hj : j ≤ J) :
    ‖iteratedFDeriv ℝ j (fun k => a * (Real.fourierChar (inner ℝ v k) : ℂ)) k‖ ≤
      (2*Real.pi)^J*(1+‖v‖)^J*‖a‖ := by
  have he : (fun k : Mom d => a * (Real.fourierChar (inner ℝ v k) : ℂ)) =
      fun k => a • (Real.fourierChar (inner ℝ v k) : ℂ) := rfl
  rw [he,iteratedFDeriv_const_smul_apply' ((contDiff_momentumModulation v).of_le
    (show (j : ℕ∞ω) ≤ ∞ by simp)).contDiffAt,norm_smul]
  have hp : (2*Real.pi)^j ≤ (2*Real.pi)^J :=
    pow_le_pow_right₀ (by nlinarith [Real.pi_gt_three]) hj
  have hv : ‖v‖^j ≤ (1+‖v‖)^J :=
    (pow_le_pow_left₀ (norm_nonneg _) (by linarith) j).trans
      (pow_le_pow_right₀ (by linarith [norm_nonneg v]) hj)
  calc
    _ ≤ ‖a‖*((2*Real.pi)^j*‖v‖^j) :=
      mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_momentumModulation_le v k j) (norm_nonneg _)
    _ ≤ ‖a‖*((2*Real.pi)^J*(1+‖v‖)^J) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hp hv (by positivity) (by positivity)) (norm_nonneg _)
    _ = _ := by ring

/-- The full masked modulation has the same dimensional spatial constant
as the landed source amplitude estimate. -/
theorem norm_iteratedFDeriv_maskedModulation_le {d m J j : ℕ}
    (c : Fin m → Fin d → ℤ) (a : ℂ) (v k : Mom d) (hj : j ≤ J) :
    ‖iteratedFDeriv ℝ j (maskedModulation c a v) k‖ ≤
      (2:ℝ)^J*rootMaskDerivativeConstant d J*(2*Real.pi)^J*(1+‖v‖)^J*‖a‖ := by
  have hD : 0 ≤ rootMaskDerivativeConstant d J := zero_le_one.trans (one_le_rootMaskDerivativeConstant d J)
  have hp := norm_iteratedFDeriv_mul_le (contDiff_sourceRootMask c)
    ((contDiff_momentumModulation v).const_smul a) k (show (j : ℕ∞ω) ≤ ∞ by simp)
  apply hp.trans
  calc
    _ ≤ ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ)*rootMaskDerivativeConstant d J*
        ((2*Real.pi)^J*(1+‖v‖)^J*‖a‖) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_sourceRootMask_le c
          ((Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hj) k) (Nat.cast_nonneg _))
        (norm_iteratedFDeriv_scalar_modulation_le a v k ((Nat.sub_le j i).trans hj))
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hD)
    _ = (2:ℝ)^j*rootMaskDerivativeConstant d J*((2*Real.pi)^J*(1+‖v‖)^J*‖a‖) := by
      rw [← Finset.sum_mul,← Finset.sum_mul]
      have hchoose : (∑ i ∈ Finset.range (j+1), (j.choose i : ℝ)) = (2:ℝ)^j := by
        exact_mod_cast Nat.sum_range_choose j
      rw [hchoose]
    _ ≤ _ := by
      have htwo := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hj
      have hrest : 0 ≤ rootMaskDerivativeConstant d J*((2*Real.pi)^J*(1+‖v‖)^J*‖a‖) := by positivity
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right htwo hrest

/-- The actual compact root mask transfers every root weight to the
localization centers before summing them. -/
theorem weighted_norm_iteratedFDeriv_maskedModulation_le {d m J j W : ℕ}
    (c : Fin m → Fin d → ℤ) (a : ℂ) (v k : Mom d) (hj : j ≤ J) :
    Fourier.momentumBracket k^W * ‖iteratedFDeriv ℝ j (maskedModulation c a v) k‖ ≤
      maskedSourceSpatialConstant d m J W *
        (∏ i, Fourier.momentumBracket (NTSP.intVec (c i))^W) * (1+‖v‖)^J * ‖a‖ := by
  have hcent : 0 ≤ ∏ i, Fourier.momentumBracket (NTSP.intVec (c i))^W :=
    Finset.prod_nonneg (fun _ _ => pow_nonneg (zero_le_one.trans (one_le_momentumBracket _)) W)
  have hD : 0 ≤ rootMaskDerivativeConstant d J := zero_le_one.trans (one_le_rootMaskDerivativeConstant d J)
  have hConst : 0 ≤ maskedSourceSpatialConstant d m J W := by
    unfold maskedSourceSpatialConstant
    positivity
  by_cases hk : k ∈ tsupport (sourceRootMask c)
  · have hw := momentumBracket_pow_le_on_sourceRootMask (W := W) c k hk
    have hd := norm_iteratedFDeriv_maskedModulation_le c a v k hj
    apply (mul_le_mul hw hd (norm_nonneg _) (by positivity)).trans_eq
    unfold maskedSourceSpatialConstant
    ring
  · have hz : iteratedFDeriv ℝ j (maskedModulation c a v) k = 0 := by
      by_contra hn
      have hs := support_iteratedFDeriv_subset j hn
      exact hk (tsupport_mul_subset_left hs)
    rw [hz,norm_zero,mul_zero]
    positivity

end WaveTurbulence.RegAsymp
