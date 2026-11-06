/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
/-! TARGET L2224-L2227 (finalproof2): the stage-1 prefactor of (redvine2) times the interpolated
bound (finalproof1) of the spliced kernel gives the per-class bound. Pure real arithmetic, with the
numerical constraints of the parameter prefix as explicit hypotheses (`nu <= eta^7`, `eta <= 1/4`,
`10 nu <= 1/2`, `delta <= 1`). -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine

theorem class_piece_bound {C δ L η ν : ℝ} {n nsb R m : ℕ} {W X H gsk bsk qsk gsb ρsb : ℝ}
    (hC : 1 ≤ C) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hL : 1 ≤ L)
    (hν : 0 < ν) (hν1 : 10 * ν ≤ 1 / 2) (hνη : ν ≤ η ^ 7) (hη : 0 < η) (hη4 : η ≤ 1 / 4)
    (hnsb : nsb ≤ n) (hgsk : 0 ≤ gsk) (hbsk : 0 ≤ bsk) (hqsk : 0 ≤ qsk) (hgsb : 0 ≤ gsb)
    (hρsb : 0 ≤ ρsb) (hH : 0 ≤ H) (hW0 : 0 ≤ W) (hX0 : 0 ≤ X)
    (hW : W ≤ (C * Real.sqrt δ) ^ (n - nsb) * C ^ m * L ^ (-η ^ 8 * gsk - η ^ 2 / 2 * bsk + η ^ 7 * qsk))
    (hX : X ≤ H * Real.exp ((nsb : ℝ) * (Real.log C + 10 * ν * Real.log δ) +
      (-40 * ν * η * gsb - η ^ 6 * (ρsb + qsk) / 2 - ((R : ℝ) - 1) * (1 / 4 + 1 / 60)) *
        Real.log L)) :
    W * X ≤ H * (C * δ ^ (10 * ν)) ^ n * C ^ m * L ^ (-(ν * η) * (gsk + gsb)) *
      L ^ (-η ^ 6 * (ρsb + qsk) / 4) * L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlogδ : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ1
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  -- exponential form of the prefactor
  have hsq : C * Real.sqrt δ = Real.exp (Real.log C + Real.log δ / 2) := by
    rw [Real.exp_add, Real.exp_log hC0, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hδ]
    congr 2; ring
  have hCn : C ^ m = Real.exp ((m : ℝ) * Real.log C) := by
    rw [Real.exp_nat_mul, Real.exp_log hC0]
  have hW' : W ≤ Real.exp (((n - nsb : ℕ) : ℝ) * (Real.log C + Real.log δ / 2) +
      (-η ^ 8 * gsk - η ^ 2 / 2 * bsk + η ^ 7 * qsk) * Real.log L + (m : ℝ) * Real.log C) := by
    refine hW.trans (le_of_eq ?_)
    rw [hsq, ← Real.exp_nat_mul, Real.rpow_def_of_pos hL0, hCn, ← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  have hR1 : (C * δ ^ (10 * ν)) = Real.exp (Real.log C + 10 * ν * Real.log δ) := by
    rw [Real.exp_add, Real.exp_log hC0, Real.rpow_def_of_pos hδ]
    congr 2; ring
  have hRHS : H * (C * δ ^ (10 * ν)) ^ n * C ^ m * L ^ (-(ν * η) * (gsk + gsb)) *
      L ^ (-η ^ 6 * (ρsb + qsk) / 4) * L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) =
      H * Real.exp ((m : ℝ) * Real.log C + (n : ℝ) * (Real.log C + 10 * ν * Real.log δ) +
        (-(ν * η) * (gsk + gsb) - η ^ 6 * (ρsb + qsk) / 4 -
          ((R : ℝ) - 1) * (1 / 4 + 1 / 60)) * Real.log L) := by
    rw [hR1, ← Real.exp_nat_mul, hCn]
    simp only [Real.rpow_def_of_pos hL0]
    rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
      ← Real.exp_add]
    congr 2
    ring
  rw [hRHS]
  have hprod : W * X ≤ Real.exp (((n - nsb : ℕ) : ℝ) * (Real.log C + Real.log δ / 2) +
      (-η ^ 8 * gsk - η ^ 2 / 2 * bsk + η ^ 7 * qsk) * Real.log L + (m : ℝ) * Real.log C) *
      (H * Real.exp ((nsb : ℝ) * (Real.log C + 10 * ν * Real.log δ) +
        (-40 * ν * η * gsb - η ^ 6 * (ρsb + qsk) / 2 - ((R : ℝ) - 1) * (1 / 4 + 1 / 60)) *
          Real.log L)) :=
    mul_le_mul hW' hX hX0 (Real.exp_pos _).le
  refine hprod.trans ?_
  rw [mul_comm, mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ hH
  apply Real.exp_le_exp.mpr
  have hnat : ((n - nsb : ℕ) : ℝ) = (n : ℝ) - nsb := by
    rw [Nat.cast_sub hnsb]
  rw [hnat]
  have h1 : ((n : ℝ) - nsb) * (Real.log C + Real.log δ / 2) ≤
      ((n : ℝ) - nsb) * (Real.log C + 10 * ν * Real.log δ) := by
    apply mul_le_mul_of_nonneg_left _ (by
      have : (nsb : ℝ) ≤ n := by exact_mod_cast hnsb
      linarith)
    nlinarith
  have hη8 : ν * η ≤ η ^ 8 := by
    have : η ^ 8 = η * η ^ 7 := by ring
    rw [this]; nlinarith
  have hη7 : η ^ 7 ≤ η ^ 6 / 4 := by
    have : η ^ 7 = η ^ 6 * η := by ring
    rw [this]
    have : 0 ≤ η ^ 6 := by positivity
    nlinarith
  have ha : ν * η * gsk ≤ η ^ 8 * gsk := mul_le_mul_of_nonneg_right hη8 hgsk
  have hb : η ^ 2 / 2 * bsk ≥ 0 := by positivity
  have hc : ν * η * gsb ≤ 40 * ν * η * gsb := by
    have : 0 ≤ ν * η * gsb := by positivity
    linarith only [this]
  have hd : η ^ 7 * qsk ≤ η ^ 6 / 4 * qsk := mul_le_mul_of_nonneg_right hη7 hqsk
  have he : 0 ≤ η ^ 6 / 4 * ρsb := by positivity
  have hcoef : (-η ^ 8 * gsk - η ^ 2 / 2 * bsk + η ^ 7 * qsk) +
      (-40 * ν * η * gsb - η ^ 6 * (ρsb + qsk) / 2 - ((R : ℝ) - 1) * (1 / 4 + 1 / 60)) ≤
      (-(ν * η) * (gsk + gsb) - η ^ 6 * (ρsb + qsk) / 4 -
          ((R : ℝ) - 1) * (1 / 4 + 1 / 60)) := by linarith
  have h2 := mul_le_mul_of_nonneg_right hcoef hlogL
  linarith only [h1, h2]

end WaveTurbulence.LGSpine
