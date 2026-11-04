/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.ScalarPowerKernel
public import WaveTurbulence.Foundations.Fourier.TimeWeights
import Mathlib.Tactic

/-!
# Splitting the positive endpoint weight among its three coordinates

A nonnegative power of the maximum bracket is bounded by the sum of the
three coordinate powers. At regularity 1/4 this assigns order 3/4 to one
endpoint denominator and retains order one in the other two.
-/

public section

open Finset
open scoped ENNReal

namespace WaveTurbulence.Sumint

/-- A nonnegative maximum-bracket power is dominated by the coordinate sum. -/
theorem timeBracket_rpow_le_sum {a : ℝ} (ha : 0 ≤ a) (ξ : Fin 3 → ℝ) :
    Fourier.timeBracket ξ^a ≤ ∑ j : Fin 3, scalarBracket (ξ j)^a := by
  have hn (j : Fin 3) : 0 ≤ scalarBracket (ξ j)^a :=
    Real.rpow_nonneg (zero_le_one.trans (one_le_scalarBracket _)) _
  have hb : ∃ j : Option (Fin 3), Fourier.timeBracket ξ =
      match j with | none => 1 | some i => scalarBracket (ξ i) := by
    unfold Fourier.timeBracket
    obtain ⟨j,_,hj⟩ := Finset.exists_mem_eq_sup' (univ_nonempty : (univ : Finset (Option (Fin 3))).Nonempty)
      (fun j : Option (Fin 3) => match j with | none => 1 | some i => scalarBracket (ξ i))
    exact ⟨j,hj⟩
  obtain ⟨j,hj⟩ := hb
  cases j with
  | none =>
    rw [hj,Real.one_rpow]
    have h0 : 1 ≤ scalarBracket (ξ 0)^a := by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1)
        (one_le_scalarBracket (ξ 0)) ha
    exact h0.trans (Finset.single_le_sum (fun j _ => hn j) (mem_univ 0))
  | some i =>
    rw [hj]
    exact Finset.single_le_sum (fun j _ => hn j) (mem_univ i)

/-- The positive endpoint weight leaves exactly one denominator of order 3/4
in each of three summands. -/
theorem endpoint_weight_kernel_split (ξ : Fin 3 → ℝ) :
    Fourier.timeWeight ((1:ℝ)/4) ξ * scalarPowerKernel 1 (ξ 0) *
      scalarPowerKernel 1 (ξ 1) * scalarPowerKernel 1 (ξ 2) ≤
      scalarPowerKernel ((3:ℝ)/4) (ξ 0)*scalarPowerKernel 1 (ξ 1)*scalarPowerKernel 1 (ξ 2) +
      scalarPowerKernel 1 (ξ 0)*scalarPowerKernel ((3:ℝ)/4) (ξ 1)*scalarPowerKernel 1 (ξ 2) +
      scalarPowerKernel 1 (ξ 0)*scalarPowerKernel 1 (ξ 1)*scalarPowerKernel ((3:ℝ)/4) (ξ 2) := by
  have hb (j : Fin 3) : 0 ≤ scalarBracket (ξ j) := zero_le_one.trans (one_le_scalarBracket _)
  have he (j : Fin 3) : scalarBracket (ξ j)^((1:ℝ)/4)*scalarBracket (ξ j)^(-1:ℝ) =
      scalarBracket (ξ j)^(-((3:ℝ)/4)) := by
    rw [← Real.rpow_add (zero_lt_one.trans_le (one_le_scalarBracket _))]
    norm_num
  have hs := timeBracket_rpow_le_sum (by norm_num : (0:ℝ) ≤ 1/4) ξ
  have hprod : 0 ≤ scalarBracket (ξ 0)^(-1:ℝ)*scalarBracket (ξ 1)^(-1:ℝ)*
      scalarBracket (ξ 2)^(-1:ℝ) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (hb 0) _) (Real.rpow_nonneg (hb 1) _))
      (Real.rpow_nonneg (hb 2) _)
  have hh := mul_le_mul_of_nonneg_right hs hprod
  rw [Fin.sum_univ_three] at hh
  have hdist : (scalarBracket (ξ 0)^((1:ℝ)/4)+scalarBracket (ξ 1)^((1:ℝ)/4)+
      scalarBracket (ξ 2)^((1:ℝ)/4)) * (scalarBracket (ξ 0)^(-1:ℝ)*scalarBracket (ξ 1)^(-1:ℝ)*
        scalarBracket (ξ 2)^(-1:ℝ)) =
      scalarBracket (ξ 0)^(-((3:ℝ)/4))*scalarBracket (ξ 1)^(-1:ℝ)*scalarBracket (ξ 2)^(-1:ℝ) +
      scalarBracket (ξ 0)^(-1:ℝ)*scalarBracket (ξ 1)^(-((3:ℝ)/4))*scalarBracket (ξ 2)^(-1:ℝ) +
      scalarBracket (ξ 0)^(-1:ℝ)*scalarBracket (ξ 1)^(-1:ℝ)*scalarBracket (ξ 2)^(-((3:ℝ)/4)) := by
    calc
      _ = (scalarBracket (ξ 0)^((1:ℝ)/4)*scalarBracket (ξ 0)^(-1:ℝ))*
          scalarBracket (ξ 1)^(-1:ℝ)*scalarBracket (ξ 2)^(-1:ℝ) +
        scalarBracket (ξ 0)^(-1:ℝ)*(scalarBracket (ξ 1)^((1:ℝ)/4)*scalarBracket (ξ 1)^(-1:ℝ))*
          scalarBracket (ξ 2)^(-1:ℝ) +
        scalarBracket (ξ 0)^(-1:ℝ)*scalarBracket (ξ 1)^(-1:ℝ)*
          (scalarBracket (ξ 2)^((1:ℝ)/4)*scalarBracket (ξ 2)^(-1:ℝ)) := by ring
      _ = _ := by rw [he,he,he]
  rw [hdist] at hh
  have hb0 := hb 0
  have hb1 := hb 1
  have hb2 := hb 2
  have ht := (Fourier.timeBracket_pos ξ).le
  have hreal := ENNReal.ofReal_le_ofReal hh
  simpa (disch := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_add,
    Fourier.timeWeight, scalarPowerKernel, mul_assoc] using hreal

end WaveTurbulence.Sumint
