/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Space

/-! # P4-W2 (b1): the generic spatial weight of a `𝒦` row

`spG c F G u₁ u₂ r k = c · G_r(k + u₂(r)) F_r(k + u₁(r))` (cut off to `‖r‖ ≤ 1`): all spatial factors of a piece (shifted by `0` or `εr`, possibly difference quotients) sit on the `𝒦` row, whose decay
is supplied by the factor `F` of weight `W`; `snorm_spG_le` bounds it by the product of the bounds of the two factors. -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS5C.P2 WaveTurbulence.LGSpine WaveTurbulence.VineEstS4c WaveTurbulence.VineEstS3.Eng
open scoped ENNReal

variable {d : ℕ} {A W : ℕ}

/-- The generic spatial weight of a `𝒦` row: `c · G_r(k + u₂(r)) · F_r(k + u₁(r))`, cut off to `‖r‖ ≤ 1`. -/
noncomputable def spG (c : ℝ) (F G : Mom d → Mom d → ℂ) (u1 u2 : Mom d → Mom d) : Mom d → Mom d → ℂ :=
  cutW fun r k => (c : ℂ) * (G r (k + u2 r) * F r (k + u1 r))

theorem snorm_spG_le (hd : 1 ≤ d) (hA : A ≠ 0) (c : ℝ) (F G : Mom d → Mom d → ℂ) (u1 u2 : Mom d → Mom d)
    (hu1 : ∀ r, ‖r‖ ≤ 1 → ‖u1 r‖ ≤ 1) (hu2 : ∀ r, ‖r‖ ≤ 1 → ‖u2 r‖ ≤ 1) {βF βG : ℝ} (hF0 : 0 ≤ βF) (hG0 : 0 ≤ βG)
    (hF : ∀ r, ‖r‖ ≤ 1 → SNorm A W (F r) ≤ ENNReal.ofReal βF)
    (hG : ∀ r, ‖r‖ ≤ 1 → SNorm A 0 (G r) ≤ ENNReal.ofReal βG) :
    ⨆ r : Mom d, SNorm A W (spG c F G u1 u2 r) ≤
      ENNReal.ofReal (|c| * ((2 : ℝ) ^ A * (d : ℝ) ^ A * ((2 : ℝ) ^ 0 * (d : ℝ) ^ A * βG) * ((2 : ℝ) ^ W * (d : ℝ) ^ A * βF))) := by
  refine snorm_cutW_le _ fun r hr => ?_
  have hFc : ContDiff ℝ A (F r) := contDiff_of_SNorm_le' hA (F r) βF (hF r hr)
  have hGc : ContDiff ℝ A (G r) := contDiff_of_SNorm_le' hA (G r) βG (hG r hr)
  have hFt := SNorm_translate_le hd hFc hF0 (hF r hr) (u1 r) (hu1 r hr)
  have hGt := SNorm_translate_le hd hGc hG0 (hG r hr) (u2 r) (hu2 r hr)
  have hFc' : ContDiff ℝ A fun k => F r (k + u1 r) := hFc.comp (contDiff_id.add contDiff_const)
  have hGc' : ContDiff ℝ A fun k => G r (k + u2 r) := hGc.comp (contDiff_id.add contDiff_const)
  have hb : 0 ≤ (2 : ℝ) ^ W * (d : ℝ) ^ A * βF := by positivity
  have hb' : 0 ≤ (2 : ℝ) ^ 0 * (d : ℝ) ^ A * βG := by positivity
  have h := SNorm_mul_le hd _ _ hGc' hFc' hb' hb hGt hFt
  refine (SNorm_smul_le A W (c : ℂ) _).trans ?_
  rw [ENNReal.ofReal_mul (abs_nonneg c)]
  refine mul_le_mul' (le_of_eq ?_) h
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]

end WaveTurbulence.VineEstS5C.P4.W2
