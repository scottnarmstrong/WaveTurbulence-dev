/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.AProcessOptimization
import Mathlib.Tactic

/-!
# A-process optimization in all frequency regimes

For the usual exponent-coordinate ranges and frequency scale at least one,
the balanced upper cutoff is automatic. When the balancing cutoff falls
below one, the trivial finite-sum estimate suffices. These theorems consume
actual shift sums and do not define a competing exponent-pair predicate.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- The A-transform estimate for every `Y >= 1`, including the regime in
which the formal optimal cutoff is smaller than one. The phase-class A
closure can use this helper once its actual differenced sums are supplied. -/
theorem weyl_vdC_norm_le_A_exponents_of_one_le (f : ℤ → ℝ) (a : ℤ) (N : ℕ)
    {Y kappa lambda : ℝ} (hN : 0 < N) (hY : 1 ≤ Y)
    (hk : 0 ≤ kappa) (hkl : kappa ≤ lambda)
    (hshift : ∀ h : ℤ, h ≠ 0 → |h| ≤ (N:ℤ) →
      ‖∑ n ∈ (Finset.Ioc a (a+N)).filter (fun n => n+h ∈ Finset.Ioc a (a+N)),
        expPhase (f (n+h)-f n)‖ ≤
          (Y^kappa*(N:ℝ)^(lambda-kappa))*|(h:ℝ)|^kappa) :
    ‖∑ n ∈ Finset.Ioc a (a+N), expPhase (f n)‖ ≤
      3*Y^(kappa/(2*kappa+2))*(N:ℝ)^((kappa+lambda+1)/(2*kappa+2)) := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNR : 0 < (N:ℝ) := zero_lt_one.trans_le hN1
  have hYR : 0 < Y := zero_lt_one.trans_le hY
  let A : ℝ := Y^kappa*(N:ℝ)^(lambda-kappa)
  let X : ℝ := ((N:ℝ)/A)^(1/(1+kappa))
  have hA1 : 1 ≤ A := by
    have hy := Real.one_le_rpow hY hk
    have hn := Real.one_le_rpow hN1 (sub_nonneg.mpr hkl)
    dsimp only [A]
    nlinarith only [hy,hn,mul_nonneg (sub_nonneg.mpr hy) (sub_nonneg.mpr hn)]
  have hAp : 0 < A := zero_lt_one.trans_le hA1
  have hXp : 0 < X := Real.rpow_pos_of_pos (div_pos hNR hAp) _
  have hp : 0 ≤ (1:ℝ)/(1+kappa) := by positivity
  have hden : 0 < 1+kappa := by linarith only [hk]
  have hp1 : (1:ℝ)/(1+kappa) ≤ 1 := by
    apply (div_le_one hden).mpr
    linarith only [hk]
  have hXN : X ≤ (N:ℝ) :=
    (Real.rpow_le_rpow (div_nonneg hNR.le hAp.le) (div_le_self hNR.le hA1) hp).trans
      (Real.rpow_le_self_of_one_le hN1 hp1)
  by_cases hX1 : 1 ≤ X
  · exact weyl_vdC_norm_le_A_exponents f a N hN hYR hk hX1 hXN hshift
  · have hnorm : ‖∑ n ∈ Finset.Ioc a (a+N), expPhase (f n)‖ ≤ (N:ℝ) := by
      have hc : (Finset.Ioc a (a+N)).card = N := by rw [Int.card_Ioc]; omega
      calc
        _ ≤ ∑ n ∈ Finset.Ioc a (a+N), ‖expPhase (f n)‖ := norm_sum_le _ _
        _ = (N:ℝ) := by simp only [norm_expPhase,Finset.sum_const,nsmul_eq_mul,mul_one,hc]
    have hsqrt : 0 < Real.sqrt X := Real.sqrt_pos.mpr hXp
    have hsqrt1 : Real.sqrt X ≤ 1 := Real.sqrt_le_iff.mpr ⟨by norm_num,
      by simpa only [one_pow] using (le_of_not_ge hX1)⟩
    have hbig : (N:ℝ) ≤ 3*(N:ℝ)/Real.sqrt X := by
      apply (le_div_iff₀ hsqrt).mpr
      nlinarith only [hNR,mul_le_mul_of_nonneg_left hsqrt1 hNR.le]
    have he := a_process_norm_scale_identity (lambda := lambda) hNR hYR hk
    change (N:ℝ)/Real.sqrt X = _ at he
    calc
      _ ≤ (N:ℝ) := hnorm
      _ ≤ 3*(N:ℝ)/Real.sqrt X := hbig
      _ = 3*((N:ℝ)/Real.sqrt X) := by ring
      _ = _ := by rw [he]; ring

end WaveTurbulence.NumberTheory
