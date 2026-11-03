/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.CircleDualScaleNormalization
public import WaveTurbulence.Foundations.NumberTheory.FifthDerivativeLinearPhase
import Mathlib.Tactic

/-!
# Actual derivative formulas imply the circle dual A-scale bound

This distinct conditional helper consumes an actual derivative tower and
its literal third/fourth/fifth formulas. Their calculus proofs remain in
VdCB. The A-process, scalar bounds, fixed comparison constants, arbitrary
linear phases and all frequency regimes are proved here.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- The pure dual-curve A-scale with explicit absolute constant, uniform in
all real added linear phases and actual integer subwindows. This does not
claim the B-process or assert a separate exponent-pair predicate. -/
theorem circle_dual_exp_sum_le_of_derivative_formulas
    (F : ℕ → ℝ → ℝ) (a : ℤ) (N : ℕ) (p q : ℝ) {R h Y : ℝ}
    (hR : 0 < R) (hh : 0 < h) (hY : 1 ≤ Y) (hhY : h ≤ Y)
    (hRY : Y^2 ≤ R*h^2) (ha : Y ≤ (a:ℝ)+1) (hb : (a:ℝ)+N+2 ≤ 4*Y)
    (hNY : (N:ℝ) ≤ 2*Y)
    (hd : ∀ r : ℕ, r < 5 → ∀ x ∈ Set.Icc Y (4*Y), HasDerivAt (F r) (F (r+1) x) x)
    (h3 : ∀ x ∈ Set.Icc Y (4*Y),
      F 3 x = -((3*R*h^2*x)/((h^2+x^2)^2*Real.sqrt (h^2+x^2))))
    (h4 : ∀ x ∈ Set.Icc Y (4*Y),
      F 4 x = (3*R*h^2*(4*x^2-h^2))/((h^2+x^2)^3*Real.sqrt (h^2+x^2)))
    (h5 : ∀ x ∈ Set.Icc Y (4*Y),
      F 5 x = -((15*R*h^2*x*(4*x^2-3*h^2))/((h^2+x^2)^4*Real.sqrt (h^2+x^2)))) :
    ‖∑ n ∈ Finset.Ioc a (a+N), expPhase (F 0 n+p*(n:ℝ)+q)‖ ≤
      17179869184*((R*h^2/Y^2)^((1:ℝ)/30)*Y^((26:ℝ)/30)) := by
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hA : 0 < R*h^2 := mul_pos hR (sq_pos_of_pos hh)
  let T : ℝ := (R*h^2)/(32768*Y)
  let Z : ℝ := 2*Y
  have hTp : 0 < T := by dsimp only [T]; positivity
  have hZ : 1 ≤ Z := by dsimp only [Z]; linarith only [hY]
  have hKT : Z ≤ 65536*T := circle_dual_normalized_frequency_comparison hYp hRY
  have hsource (x : ℝ) (hx : x ∈ Set.Icc ((a:ℝ)+1) ((a:ℝ)+N+2)) :
      x ∈ Set.Icc Y (4*Y) := ⟨ha.trans hx.1,hx.2.trans hb⟩
  have he := norm_exp_sum_add_linear_le_of_signed_derivative_scales F a N p q
    (Y := Z) (T := T) (K := 65536) (c := 4294967296)
    hZ hTp (by norm_num) hKT hNY (by norm_num)
    (fun r hr x hx => hd r hr x (hsource x hx))
    (fun x hx => by
      have hx' := hsource x hx
      have hc := circle_dual_normalized_derivative_comparison
        (v := (3*R*h^2*x)/((h^2+x^2)^2*Real.sqrt (h^2+x^2))) hA hYp 3 (by norm_num)
        (by simpa only [mul_assoc] using! circle_dual_third_quotient_bounds hR hh hhY hx')
      rw [h3 x hx']
      exact ⟨by nlinarith only [hc.2],by nlinarith only [hc.1]⟩)
    (fun x hx => by
      have hx' := hsource x hx
      rw [h4 x hx']
      exact circle_dual_normalized_derivative_comparison hA hYp 4 (by norm_num)
        (by simpa only [mul_assoc] using! circle_dual_fourth_quotient_bounds hR hh hhY hx'))
    (fun x hx => by
      have hx' := hsource x hx
      have hc := circle_dual_normalized_derivative_comparison
        (v := (15*R*h^2*x*(4*x^2-3*h^2))/((h^2+x^2)^4*Real.sqrt (h^2+x^2))) hA hYp 5 (by norm_num)
        (by simpa only [mul_assoc] using! circle_dual_fifth_quotient_bounds hR hh hhY hx')
      rw [h5 x hx']
      exact ⟨by nlinarith only [hc.2],by nlinarith only [hc.1]⟩)
  have hsqrt : Real.sqrt (4294967296:ℝ) ≤ 65536 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have hCmax : (65536:ℝ)^2+16384*Real.sqrt 4294967296 ≤ 8589934592 := by
    nlinarith only [hsqrt]
  have hratio : T/Z ≤ R*h^2/Y^2 := by
    have hid : T/Z = ((1:ℝ)/65536)*(R*h^2/Y^2) := by
      dsimp only [T,Z]
      field_simp
      ring
    rw [hid]
    have hp : 0 ≤ R*h^2/Y^2 := by positivity
    nlinarith only [hp]
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ T/Z) hratio (by norm_num : (0:ℝ) ≤ 1/30)
  have hZpow : Z^((26:ℝ)/30) ≤ 2*Y^((26:ℝ)/30) := by
    dsimp only [Z]
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hYp.le]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_self_of_one_le (by norm_num : (1:ℝ) ≤ 2) (by norm_num : (26:ℝ)/30 ≤ 1))
      (Real.rpow_nonneg hYp.le _)
  have hprod : (T/Z)^((1:ℝ)/30)*Z^((26:ℝ)/30) ≤
      2*((R*h^2/Y^2)^((1:ℝ)/30)*Y^((26:ℝ)/30)) := by
    calc
      _ ≤ (R*h^2/Y^2)^((1:ℝ)/30)*(2*Y^((26:ℝ)/30)) :=
        mul_le_mul hpow hZpow (Real.rpow_nonneg (by positivity : 0 ≤ Z) _)
          (Real.rpow_nonneg (by positivity : 0 ≤ R*h^2/Y^2) _)
      _ = _ := by ring
  calc
    _ ≤ ((65536:ℝ)^2+16384*Real.sqrt 4294967296)*((T/Z)^((1:ℝ)/30)*Z^((26:ℝ)/30)) := he
    _ ≤ 8589934592*((T/Z)^((1:ℝ)/30)*Z^((26:ℝ)/30)) := mul_le_mul_of_nonneg_right hCmax (by positivity)
    _ ≤ 8589934592*(2*((R*h^2/Y^2)^((1:ℝ)/30)*Y^((26:ℝ)/30))) :=
      mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = _ := by ring

end WaveTurbulence.NumberTheory
