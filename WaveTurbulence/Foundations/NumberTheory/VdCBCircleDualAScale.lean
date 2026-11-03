/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.CircleDualAScale
public import WaveTurbulence.Foundations.VdCB.CircleLatticeRegularity
import Mathlib.Tactic

/-!
# The A-scale estimate for VdCB's actual integer-column dual

The shared circle-dual calculus supplies every derivative formula. The
actual exponential sum is uniform in arbitrary real linear phases and
integer subwindows. No exponent-pair predicate, derivative estimate or
B-process conclusion remains as a premise of this A-scale theorem.
-/

public section

namespace WaveTurbulence.NumberTheory

private theorem rpow_negative_half_integer {D : ℝ} (hD : 0 < D) (m : ℕ) :
    D^(-((m:ℝ)+1/2)) = 1/(D^m*Real.sqrt D) := by
  rw [Real.rpow_neg hD.le,Real.rpow_add hD,Real.rpow_natCast,← Real.sqrt_eq_rpow,one_div]

/-- Actual pure dual A-estimate, using VdCB's original integer-column dual
and including its arbitrary real translation phase. All derivative formulas
are proved internally from the landed shared calculus. -/
theorem norm_sum_circleLatticeDualPhase_add_linear_le (a : ℤ) (N : ℕ) (p q : ℝ)
    {R h Y : ℝ} (hR : 0 < R) (hh : 0 < h) (hY : 1 ≤ Y) (hhY : h ≤ Y)
    (hRY : Y^2 ≤ R*h^2) (ha : Y ≤ (a:ℝ)+1) (hb : (a:ℝ)+N+2 ≤ 4*Y)
    (hNY : (N:ℝ) ≤ 2*Y) :
    ‖∑ n ∈ Finset.Ioc a (a+N),
      expPhase (VdCB.circleLatticeDualPhase R h n+p*(n:ℝ)+q)‖ ≤
      17179869184*((R*h^2/Y^2)^((1:ℝ)/30)*Y^((26:ℝ)/30)) := by
  let f : ℝ → ℝ := VdCB.circleDualPhase R h
  have hs := VdCB.contDiff_circleDualPhase R hh
  have h1 : deriv f = VdCB.circleDualFirst R h :=
    funext fun x => (VdCB.hasDerivAt_circleDualPhase R hh x).deriv
  have h2 : deriv (VdCB.circleDualFirst R h) = VdCB.circleDualSecond R h :=
    funext fun x => (VdCB.hasDerivAt_circleDualFirst R hh x).deriv
  have h3 : deriv (VdCB.circleDualSecond R h) = VdCB.circleDualThird R h :=
    funext fun x => (VdCB.hasDerivAt_circleDualSecond R hh x).deriv
  have h4 : deriv (VdCB.circleDualThird R h) = VdCB.circleDualFourth R h :=
    funext fun x => (VdCB.hasDerivAt_circleDualThird R hh x).deriv
  have he3 : iteratedDeriv 3 f = VdCB.circleDualThird R h := by
    simp only [iteratedDeriv_succ,iteratedDeriv_zero,h1,h2,h3]
  have he4 : iteratedDeriv 4 f = VdCB.circleDualFourth R h := by
    simp only [iteratedDeriv_succ,iteratedDeriv_zero,h1,h2,h3,h4]
  have he5 : iteratedDeriv 5 f = VdCB.circleDualFifth R h := VdCB.iteratedDeriv_five_circleDualPhase R hh
  have hD (x : ℝ) : 0 < h^2+x^2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hh) (sq_nonneg x)
  have ht := circle_dual_exp_sum_le_of_derivative_formulas (fun r => iteratedDeriv r f)
    a N (p+R) q hR hh hY hhY hRY ha hb hNY
    (fun r _hr x _hx => by
      have hfinit : ContDiff ℝ (r+1) f := hs.of_le (by simp)
      have hd := (hfinit.differentiable_iteratedDeriv' r x).hasDerivAt
      simpa only [iteratedDeriv_succ,f] using! hd)
    (fun x _hx => by
      rw [he3]
      have he : (h^2+x^2)^(-((5:ℝ)/2)) = 1/((h^2+x^2)^2*Real.sqrt (h^2+x^2)) := by
        simpa only [Nat.cast_ofNat,show -((2:ℝ)+1/2) = -(5/2) by norm_num] using
          rpow_negative_half_integer (hD x) 2
      unfold VdCB.circleDualThird
      rw [he]
      ring)
    (fun x _hx => by
      rw [he4]
      have he : (h^2+x^2)^(-((7:ℝ)/2)) = 1/((h^2+x^2)^3*Real.sqrt (h^2+x^2)) := by
        simpa only [Nat.cast_ofNat,show -((3:ℝ)+1/2) = -(7/2) by norm_num] using
          rpow_negative_half_integer (hD x) 3
      unfold VdCB.circleDualFourth
      rw [he]
      ring)
    (fun x _hx => by
      rw [he5]
      have he : (h^2+x^2)^(-((9:ℝ)/2)) = 1/((h^2+x^2)^4*Real.sqrt (h^2+x^2)) := by
        simpa only [Nat.cast_ofNat,show -((4:ℝ)+1/2) = -(9/2) by norm_num] using
          rpow_negative_half_integer (hD x) 4
      unfold VdCB.circleDualFifth
      rw [he]
      ring)
  have hphase (x : ℝ) : iteratedDeriv 0 f x+(p+R)*x+q =
      VdCB.circleLatticeDualPhase R h x+p*x+q := by
    simp only [iteratedDeriv_zero,VdCB.circleLatticeDualPhase,f]
    ring
  simpa only [hphase] using ht

end WaveTurbulence.NumberTheory
