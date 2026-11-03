/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Analysis.CubeSobolev
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# A whole-space L² Sobolev estimate in extended integrals

The square-free mixed derivative energy controls point evaluation. No global
integrability hypothesis is needed: the right side is an extended nonnegative
integral, and the finite-energy application will follow in weighted jets.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.WKEL2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One-dimensional global H¹ controls every point, in squared extended-integral form. -/
theorem ofReal_norm_sq_le_global_H1 {f : ℝ → E} (hf : ContDiff ℝ 1 f) (t : ℝ) :
    ENNReal.ofReal (‖f t‖ ^ 2) ≤
      2 * ((∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2)) +
        ∫⁻ x, ENNReal.ofReal (‖deriv f x‖ ^ 2)) := by
  let A := ∫ x in Icc t (t + 1), ‖f x‖ ^ 2
  let B := ∫ x in Icc t (t + 1), ‖deriv f x‖ ^ 2
  have hA : 0 ≤ A := integral_nonneg fun _ => sq_nonneg _
  have hB : 0 ≤ B := integral_nonneg fun _ => sq_nonneg _
  have H := Analysis.norm_le_interval_sobolev_L2 hf
    (show t ∈ Icc t (t + 1) from ⟨le_rfl, by linarith⟩)
  have Hsq : ‖f t‖ ^ 2 ≤ 2 * (A + B) := by
    apply (pow_le_pow_left₀ (norm_nonneg _) H 2).trans
    simpa only [Real.sq_sqrt hA, Real.sq_sqrt hB] using
      (add_sq_le (a := Real.sqrt A) (b := Real.sqrt B))
  have hiA : IntegrableOn (fun x => ‖f x‖ ^ 2) (Icc t (t + 1)) :=
    (hf.continuous.norm.pow 2).integrableOn_Icc
  have hiB : IntegrableOn (fun x => ‖deriv f x‖ ^ 2) (Icc t (t + 1)) :=
    (hf.continuous_deriv_one.norm.pow 2).integrableOn_Icc
  have Henn := ENNReal.ofReal_le_ofReal Hsq
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add hA hB] at Henn
  dsimp only [A, B] at Henn
  rw [ofReal_integral_eq_lintegral_ofReal hiA (ae_of_all _ fun _ => sq_nonneg _),
    ofReal_integral_eq_lintegral_ofReal hiB (ae_of_all _ fun _ => sq_nonneg _)] at Henn
  norm_num only [ENNReal.ofReal_ofNat] at Henn
  exact Henn.trans (mul_le_mul_right (add_le_add
    (lintegral_mono' Measure.restrict_le_self le_rfl)
    (lintegral_mono' Measure.restrict_le_self le_rfl)) 2)

/-- Sum of the squared L² energies of all square-free mixed derivatives. -/
@[expose] def wholeSobolevL2Sq : (n : ℕ) → ((Fin n → ℝ) → E) → ℝ≥0∞
  | 0, f => ENNReal.ofReal (‖f (fun i => Fin.elim0 i)‖ ^ 2)
  | n + 1, f =>
      (∫⁻ t, wholeSobolevL2Sq n (fun x => f (Fin.cons t x))) +
      ∫⁻ t, wholeSobolevL2Sq n (fun x => deriv (fun s => f (Fin.cons s x)) t)

/-- Whole-space Sobolev embedding using only square-free derivatives of order at most n. -/
theorem ofReal_norm_sq_le_wholeSobolevL2Sq : ∀ (n : ℕ) {f : (Fin n → ℝ) → E},
    ContDiff ℝ ∞ f → ∀ x, ENNReal.ofReal (‖f x‖ ^ 2) ≤ 2 ^ n * wholeSobolevL2Sq n f := by
  intro n
  induction n with
  | zero =>
      intro f _ x
      simpa only [pow_zero, one_mul, wholeSobolevL2Sq] using
        le_of_eq (congrArg (fun y => ENNReal.ofReal (‖f y‖ ^ 2)) (Subsingleton.elim x _))
  | succ n ih =>
      intro f hf x
      have H := ofReal_norm_sq_le_global_H1
        ((hf.comp (Analysis.contDiff_cons_curve (Fin.tail x))).of_le (by simp)) (x 0)
      simp only [Function.comp_apply, Fin.cons_self_tail] at H
      apply H.trans
      calc
        _ ≤ 2 * ((∫⁻ t, 2 ^ n * wholeSobolevL2Sq n (fun y => f (Fin.cons t y))) +
            ∫⁻ t, 2 ^ n * wholeSobolevL2Sq n (fun y => deriv (fun s => f (Fin.cons s y)) t)) := by
          apply mul_le_mul_right
          apply add_le_add
          · exact lintegral_mono fun t => ih (hf.comp (Analysis.contDiff_cons_const t)) (Fin.tail x)
          · exact lintegral_mono fun t => ih (Analysis.contDiff_deriv_cons hf t) (Fin.tail x)
        _ = _ := by
          rw [lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _ (by simp),
            wholeSobolevL2Sq, pow_succ]
          ring

end WaveTurbulence.WKEL2
