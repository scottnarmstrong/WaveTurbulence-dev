/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.AProcessBounds
import Mathlib.Tactic

/-!
# The numerical exponent transformation in the A-process

For the actual shift-bound coefficient `Y^kappa * N^(lambda-kappa)`, the
balanced cutoff gives exponents `kappa/(2*kappa+2)` and
`(kappa+lambda+1)/(2*kappa+2)`. These are distinct conditional helpers, not
a second definition of exponent pairs; VdCB owns the shared phase-class API.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- The real balancing cutoff exactly balances the two A-process terms. -/
theorem a_process_balance_identity {N Y kappa lambda : ℝ}
    (hN : 0 < N) (hY : 0 < Y) (hk : 0 ≤ kappa) :
    (Y^kappa*N^(lambda-kappa))*
      (N/(Y^kappa*N^(lambda-kappa)))^((1/(1+kappa))*(1+kappa)) = N := by
  have hA : 0 < Y^kappa*N^(lambda-kappa) :=
    mul_pos (Real.rpow_pos_of_pos hY _) (Real.rpow_pos_of_pos hN _)
  have hden : 1+kappa ≠ 0 := ne_of_gt (by linarith only [hk])
  rw [one_div_mul_cancel hden,Real.rpow_one]
  field_simp

/-- Scalar identity behind the A-transform of exponent coordinates. -/
theorem a_process_norm_scale_identity {N Y kappa lambda : ℝ}
    (hN : 0 < N) (hY : 0 < Y) (hk : 0 ≤ kappa) :
    N/Real.sqrt ((N/(Y^kappa*N^(lambda-kappa)))^(1/(1+kappa))) =
      Y^(kappa/(2*kappa+2))*N^((kappa+lambda+1)/(2*kappa+2)) := by
  let A : ℝ := Y^kappa*N^(lambda-kappa)
  let t : ℝ := 1/(2*kappa+2)
  have hA : 0 < A := mul_pos (Real.rpow_pos_of_pos hY _) (Real.rpow_pos_of_pos hN _)
  have hden : 0 < 1+kappa := by linarith only [hk]
  have hden2 : 0 < 2*kappa+2 := by linarith only [hk]
  have hsqrt : Real.sqrt ((N/A)^(1/(1+kappa))) = N^t/A^t := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul (div_pos hN hA).le]
    have he : (1/(1+kappa))*((1:ℝ)/2) = t := by dsimp only [t]; field_simp; ring
    rw [he,Real.div_rpow hN.le hA.le]
  have hscale : N/(N^t/A^t) = A^t*N^(1-t) := by
    rw [Real.rpow_sub hN,Real.rpow_one]
    field_simp
  have hApow : A^t = Y^(kappa*t)*N^((lambda-kappa)*t) := by
    dsimp only [A]
    rw [Real.mul_rpow (Real.rpow_nonneg hY.le _) (Real.rpow_nonneg hN.le _),
      ← Real.rpow_mul hY.le,← Real.rpow_mul hN.le]
  have hek : kappa*t = kappa/(2*kappa+2) := by dsimp only [t]; ring
  have hel : (lambda-kappa)*t+(1-t) = (kappa+lambda+1)/(2*kappa+2) := by
    dsimp only [t]
    field_simp
    ring
  change N/Real.sqrt ((N/A)^(1/(1+kappa))) = _
  rw [hsqrt,hscale,hApow,mul_assoc,← Real.rpow_add hN,hek,hel]

/-- A-process exponent-coordinate estimate in the balanced-cutoff regime.
The phase estimates are the actual finite differenced sums, and the cutoff
regime is explicit rather than hidden inside an exponent-pair predicate. -/
theorem weyl_vdC_norm_le_A_exponents (f : ℤ → ℝ) (a : ℤ) (N : ℕ)
    {Y kappa lambda : ℝ} (hN : 0 < N) (hY : 0 < Y) (hk : 0 ≤ kappa)
    (hcut1 : 1 ≤ ((N:ℝ)/(Y^kappa*(N:ℝ)^(lambda-kappa)))^(1/(1+kappa)))
    (hcutN : ((N:ℝ)/(Y^kappa*(N:ℝ)^(lambda-kappa)))^(1/(1+kappa)) ≤ (N:ℝ))
    (hshift : ∀ h : ℤ, h ≠ 0 → |h| ≤ (N:ℤ) →
      ‖∑ n ∈ (Finset.Ioc a (a+N)).filter (fun n => n+h ∈ Finset.Ioc a (a+N)),
        expPhase (f (n+h)-f n)‖ ≤
          (Y^kappa*(N:ℝ)^(lambda-kappa))*|(h:ℝ)|^kappa) :
    ‖∑ n ∈ Finset.Ioc a (a+N), expPhase (f n)‖ ≤
      3*Y^(kappa/(2*kappa+2))*(N:ℝ)^((kappa+lambda+1)/(2*kappa+2)) := by
  have hNR : 0 < (N:ℝ) := by exact_mod_cast hN
  have hA : 0 ≤ Y^kappa*(N:ℝ)^(lambda-kappa) := by positivity
  have hratio : 0 ≤ (N:ℝ)/(Y^kappa*(N:ℝ)^(lambda-kappa)) := by positivity
  have hbalance : (Y^kappa*(N:ℝ)^(lambda-kappa))*
      (((N:ℝ)/(Y^kappa*(N:ℝ)^(lambda-kappa)))^(1/(1+kappa)))^(kappa+1) ≤ (N:ℝ) := by
    rw [← Real.rpow_mul hratio]
    have he : kappa+1 = 1+kappa := by ring
    rw [he,a_process_balance_identity hNR hY hk]
  have hb := weyl_vdC_norm_le_balanced f a N hA hk hcut1 hcutN hbalance hshift
  have he := a_process_norm_scale_identity (lambda := lambda) hNR hY hk
  calc
    _ ≤ 3*(N:ℝ)/Real.sqrt (((N:ℝ)/(Y^kappa*(N:ℝ)^(lambda-kappa)))^(1/(1+kappa))) := hb
    _ = 3*((N:ℝ)/Real.sqrt (((N:ℝ)/(Y^kappa*(N:ℝ)^(lambda-kappa)))^(1/(1+kappa)))) := by ring
    _ = _ := by rw [he]; ring

end WaveTurbulence.NumberTheory
