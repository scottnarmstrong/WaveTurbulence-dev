/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.AProcessDerivativeBalance
import Mathlib.Tactic

/-!
# Complete numerical A-step for higher derivative tests

The derivative-test powers transform as
`(alpha,b) -> (alpha/(2*alpha+2),(b+1)/2)`. The empty, small-cutoff and
large-cutoff regimes are included using the actual trivial finite-sum bound.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- A complete A-step retaining both derivative-test powers, from the
actual finite differenced sums in the Weyl inequality. -/
theorem weyl_vdC_norm_le_derivative_step (f : ℤ → ℝ) (a : ℤ) (N : ℕ)
    {lam D alpha b : ℝ} (hlam : 0 < lam) (hD : 1 ≤ D)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hb : 0 ≤ b)
    (hshift : ∀ h : ℕ, 0 < h → h ≤ N →
      ‖∑ n ∈ (Finset.Ioc a (a+N)).filter (fun n => n+(h:ℤ) ∈ Finset.Ioc a (a+N)),
        expPhase (f (n+h)-f n)‖ ≤
          D*((N:ℝ)*(lam*(h:ℝ))^alpha+(N:ℝ)^b*(lam*(h:ℝ))^(-alpha))) :
    ‖∑ n ∈ Finset.Ioc a (a+N), expPhase (f n)‖ ≤
      (16*D/(1-alpha))*((N:ℝ)*lam^(alpha/(2*alpha+2))+
        (N:ℝ)^((b+1)/2)*lam^(-(alpha/(2*alpha+2)))) := by
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  have hden : 0 < 1-alpha := sub_pos.mpr ha1
  by_cases hN : 0 < N
  swap
  · have hN0 : N = 0 := by omega
    subst N
    simp only [Nat.cast_zero,add_zero,Finset.Ioc_self,Finset.sum_empty,norm_zero]
    positivity
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNR : 0 < (N:ℝ) := zero_lt_one.trans_le hN1
  have haden : 0 < alpha+1 := by linarith only [ha]
  let beta : ℝ := alpha/(2*alpha+2)
  let X : ℝ := lam^(-(alpha/(alpha+1)))
  let x : ℝ := (N:ℝ)*lam^beta
  let y : ℝ := (N:ℝ)^((b+1)/2)*lam^(-beta)
  let K : ℝ := 16*D/(1-alpha)
  have hbeta : 0 ≤ beta := by dsimp only [beta]; positivity
  have hKlo : 16*D ≤ K := by
    apply (le_div_iff₀ hden).mpr
    nlinarith only [mul_nonneg hD0 ha.le]
  have hK1 : 1 ≤ K := by linarith only [hD,hKlo]
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hy0 : 0 ≤ y := by dsimp only [y]; positivity
  have htriv : ‖∑ n ∈ Finset.Ioc a (a+N), expPhase (f n)‖ ≤ (N:ℝ) := by
    have hc : (Finset.Ioc a (a+N)).card = N := by rw [Int.card_Ioc]; omega
    calc
      _ ≤ ∑ n ∈ Finset.Ioc a (a+N), ‖expPhase (f n)‖ := norm_sum_le _ _
      _ = (N:ℝ) := by simp only [norm_expPhase,Finset.sum_const,nsmul_eq_mul,mul_one,hc]
  have hfinish (hxy : (N:ℝ) ≤ x+y) :
      ‖∑ n ∈ Finset.Ioc a (a+N), expPhase (f n)‖ ≤ K*(x+y) := by
    apply htriv.trans
    calc
      _ ≤ x+y := hxy
      _ ≤ _ := by nlinarith only [mul_nonneg (sub_nonneg.mpr hK1) (add_nonneg hx0 hy0)]
  by_cases hlarge : 1 ≤ lam
  · apply hfinish
    have hu := Real.one_le_rpow hlarge hbeta
    have hx : (N:ℝ) ≤ x := by
      dsimp only [x]
      nlinarith only [mul_le_mul_of_nonneg_left hu hNR.le]
    linarith only [hx,hy0]
  have hX1 : 1 ≤ X := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hlam (le_of_not_ge hlarge)
    (neg_nonpos.mpr (div_nonneg ha.le haden.le))
  by_cases hXN : X ≤ (N:ℝ)
  · exact weyl_vdC_norm_le_derivative_balance f a N hN hlam hD ha ha1 hX1 hXN hshift
  · apply hfinish
    have he : alpha/(alpha+1) = 2*beta := by
      dsimp only [beta]
      field_simp
    have hV : lam^(-beta) = Real.sqrt X := by
      dsimp only [X]
      rw [Real.sqrt_eq_rpow,← Real.rpow_mul hlam.le,he]
      congr 1
      ring
    have hpow : Real.sqrt (N:ℝ) ≤ (N:ℝ)^((b+1)/2) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hb])
    have hsqrt : Real.sqrt (N:ℝ) ≤ Real.sqrt X := Real.sqrt_le_sqrt (le_of_not_ge hXN)
    have hNy : (N:ℝ) ≤ y := by
      calc
        _ = Real.sqrt (N:ℝ)*Real.sqrt (N:ℝ) := (Real.mul_self_sqrt hNR.le).symm
        _ ≤ (N:ℝ)^((b+1)/2)*Real.sqrt X := mul_le_mul hpow hsqrt
          (Real.sqrt_nonneg _) (Real.rpow_nonneg hNR.le _)
        _ = y := by dsimp only [y]; rw [hV]
    linarith only [hx0,hNy]

end WaveTurbulence.NumberTheory
