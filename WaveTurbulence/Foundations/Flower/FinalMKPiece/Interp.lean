/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SplicedScaleInterpolation

/-! # C5a PIECE-MK: the 40ν interpolation with a crude `cθ^n` and extra exponents

Main's `spliced_scale_interpolation` with (i) a factor `cθ^n` in the crude bound and (ii) extra exponents `e1`
(crude, the split cost `80 d |split|`) and `e2` (fine, `2 N_E` and the pin scale loss). The interpolated exponent
carries `40ν e1 + e2` and `cθ^{40ν n}`. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.FinalMKPiece
open WaveTurbulence.LGSpine

/-- The scalar interpolation step with extras. -/
theorem mk_interpolation_exp {z : ℂ} {η ν d ρ g R n c l u κ e1 e2 : ℝ}
    (hν : 0 ≤ ν) (hsmall : 40 * ν ≤ 1 / 100) (hcost : 3200 * d * ν ≤ η ^ 6 / 4)
    (hρ : 0 ≤ ρ) (hR : 1 ≤ R) (hn : 0 ≤ n) (hl : 0 ≤ l) (hu : u ≤ 0) (_hκ : 0 ≤ κ) (he2 : 0 ≤ e2)
    (hcoarse : ‖z‖ ≤ Real.exp (n * (c + u / 2 + κ) + (-η * g + 80 * d * ρ + e1) * l))
    (hcount : ‖z‖ ≤ Real.exp (n * (c - 10 * ν * u) +
      (-η ^ 6 * ρ - (R - 1) * (1 / 4 + 1 / 50) + e2) * l)) :
    ‖z‖ ≤ Real.exp (n * (c + 10 * ν * u + 40 * ν * κ) +
      (-40 * ν * η * g - η ^ 6 * ρ / 2 - (R - 1) * (1 / 4 + 1 / 60) + 40 * ν * e1 + e2) * l) := by
  have haWeight0 : 0 ≤ 40 * ν := mul_nonneg (by norm_num) hν
  have haWeight1 : 40 * ν ≤ 1 := by linarith
  apply (norm_le_exp_interpolation hcoarse hcount haWeight0 haWeight1).trans
  apply Real.exp_le_exp.mpr
  have hL := mul_le_mul_of_nonneg_right
    (spliced_L_exponent_le (g := g) hν (by positivity : 0 ≤ η ^ 6) hsmall hcost hρ hR) hl
  have hδ := mul_le_mul_of_nonpos_right (spliced_delta_exponent_ge ν) hu
  have hδn := mul_le_mul_of_nonneg_left hδ hn
  have h1 : (1 - 40 * ν) * e2 * l ≤ e2 * l := by
    have : (1 - 40 * ν) * e2 ≤ e2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hl
  nlinarith

/-- Interpolation in power form: crude `H (cθ C √δ)^n L^{-ηg + 80dρ + e1}`, fine
`C (C δ^{-10ν})^n L^{-η⁶ρ} L^{-(R-1)(1/4+1/50)} L^{e2}`. -/
theorem mk_interpolation {z : ℂ} {C H δ L η ν d ρ g R cθ e1 e2 : ℝ} (n : ℕ)
    (hC : 0 < C) (hH : 0 < H) (hCH : C ≤ H) (hcθ : 1 ≤ cθ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hL : 1 ≤ L)
    (hν : 0 ≤ ν) (hsmall : 40 * ν ≤ 1 / 100)
    (hcost : 3200 * d * ν ≤ η ^ 6 / 4) (hρ : 0 ≤ ρ) (hR : 1 ≤ R) (he2 : 0 ≤ e2)
    (hc : ‖z‖ ≤ H * (cθ * C * Real.sqrt δ) ^ n * L ^ (-η * g + 80 * d * ρ + e1))
    (hf : ‖z‖ ≤ C * (C * δ ^ (-10 * ν)) ^ n * L ^ (-η ^ 6 * ρ) *
      L ^ (-(R - 1) * (1 / 4 + 1 / 50)) * L ^ e2) :
    ‖z‖ ≤ H * Real.exp ((n : ℝ) * (Real.log C + 10 * ν * Real.log δ + 40 * ν * Real.log cθ) +
      (-40 * ν * η * g - η ^ 6 * ρ / 2 - (R - 1) * (1 / 4 + 1 / 60) + 40 * ν * e1 + e2) * Real.log L) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hcC : 0 < cθ * C := mul_pos (by linarith) hC
  have hc' : ‖z‖ ≤ H * Real.exp ((n : ℝ) * (Real.log C + Real.log δ / 2 + Real.log cθ) +
      (-η * g + 80 * d * ρ + e1) * Real.log L) := by
    rw [Real.sqrt_eq_rpow, mul_assoc H, source_scale_eq_exp hcC hδ hL0] at hc
    convert hc using 3
    rw [Real.log_mul (by linarith) hC.ne']
    ring
  have hf' : ‖z‖ ≤ H * Real.exp ((n : ℝ) * (Real.log C - 10 * ν * Real.log δ) +
      (-η ^ 6 * ρ - (R - 1) * (1 / 4 + 1 / 50) + e2) * Real.log L) := by
    have heq : C * (C * δ ^ (-10 * ν)) ^ n * L ^ (-η ^ 6 * ρ) *
        L ^ (-(R - 1) * (1 / 4 + 1 / 50)) * L ^ e2 =
        C * Real.exp ((n : ℝ) * (Real.log C - 10 * ν * Real.log δ) +
          (-η ^ 6 * ρ - (R - 1) * (1 / 4 + 1 / 50) + e2) * Real.log L) := by
      rw [mul_assoc, mul_assoc, mul_assoc, ← Real.rpow_add hL0, ← Real.rpow_add hL0,
        source_scale_eq_exp hC hδ hL0]
      congr 2; ring
    rw [heq] at hf
    exact hf.trans (mul_le_mul_of_nonneg_right hCH (Real.exp_pos _).le)
  have hnorm : ‖z / (H : ℂ)‖ = ‖z‖ / H := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
  have hb := mk_interpolation_exp (z := z / (H : ℂ)) (n := (n : ℝ)) (c := Real.log C)
    (l := Real.log L) (u := Real.log δ) (κ := Real.log cθ) (g := g) (R := R) (ρ := ρ) (e1 := e1)
    (e2 := e2) hν hsmall hcost hρ hR (Nat.cast_nonneg n) (Real.log_nonneg hL)
    (Real.log_nonpos hδ.le hδ1) (Real.log_nonneg hcθ) he2
    (by rw [hnorm]; exact (div_le_iff₀ hH).mpr (by simpa only [mul_comm] using hc'))
    (by rw [hnorm]; exact (div_le_iff₀ hH).mpr (by simpa only [mul_comm] using hf'))
  rw [hnorm] at hb
  exact (div_le_iff₀ hH).mp hb |>.trans_eq (mul_comm _ _)

end WaveTurbulence.Flower.FinalMKPiece
