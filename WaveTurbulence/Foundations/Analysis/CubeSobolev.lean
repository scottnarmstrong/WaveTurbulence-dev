/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.IntervalSobolev
public import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# The elementary cube Sobolev inequality

An iterated-integral formulation of DH21 (10.5), L2428. Each coordinate is
differentiated either zero or one times. The recursion lists the resulting
`2^n` terms without choosing an enumeration of subsets of the coordinates.
-/

public section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Sum of the `L¹` norms of all square-free mixed derivatives on the unit
cube, written as iterated Lebesgue integrals. At the recursive step, the
first term leaves the first coordinate undifferentiated, and the second
term differentiates it. Thus there are exactly `2^n` terms. Extended norms
make the definition meaningful without integrability assumptions. -/
@[expose] noncomputable def cubeSobolevL1 : (n : ℕ) → ((Fin n → ℝ) → E) → ℝ≥0∞
  | 0, f => ‖f (fun i => Fin.elim0 i)‖ₑ
  | n + 1, f =>
      (∫⁻ t in Icc (0 : ℝ) 1, cubeSobolevL1 n (fun x => f (Fin.cons t x))) +
      ∫⁻ t in Icc (0 : ℝ) 1,
        cubeSobolevL1 n (fun x => deriv (fun s => f (Fin.cons s x)) t)

theorem contDiff_cons_const {n : ℕ} (t : ℝ) :
    ContDiff ℝ ∞ (fun x : Fin n → ℝ => (Fin.cons t x : Fin (n + 1) → ℝ)) := by
  apply contDiff_pi.2
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.cons_zero] using (contDiff_const : ContDiff ℝ ∞ (fun _ : Fin n → ℝ => t))
  · simpa only [Fin.cons_succ] using contDiff_apply ℝ (fun _ : Fin n => ℝ) j

theorem contDiff_cons_curve {n : ℕ} (x : Fin n → ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ => (Fin.cons t x : Fin (n + 1) → ℝ)) := by
  apply contDiff_pi.2
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · convert (contDiff_id : ContDiff ℝ ∞ (id : ℝ → ℝ)) using 1
    ext t
    rfl
  · simpa only [Fin.cons_succ] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => x j))

theorem contDiff_deriv_cons {n : ℕ} {f : (Fin (n + 1) → ℝ) → E}
    (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    ContDiff ℝ ∞ (fun x : Fin n → ℝ => deriv (fun s => f (Fin.cons s x)) t) := by
  have hc : ContDiff ℝ ∞ (fun p : (Fin n → ℝ) × ℝ => (Fin.cons p.2 p.1 : Fin (n + 1) → ℝ)) := by
    apply contDiff_pi.2
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.cons_zero] using (contDiff_snd : ContDiff ℝ ∞
        (fun p : (Fin n → ℝ) × ℝ => p.2))
    · convert ((contDiff_apply ℝ (fun _ : Fin n => ℝ) j).comp
      (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : (Fin n → ℝ) × ℝ → Fin n → ℝ))) using 1
      ext p
      rfl
  have hfc : ContDiff ℝ ∞ (Function.uncurry
      (fun (x : Fin n → ℝ) (s : ℝ) => f (Fin.cons s x))) := hf.comp hc
  have hd := hfc.fderiv_apply (n := ∞) (g := fun _ : Fin n → ℝ => t)
    (k := fun _ : Fin n → ℝ => (1 : ℝ)) contDiff_const contDiff_const (by simp)
  simpa only [fderiv_apply_one_eq_deriv] using hd

/-- One-dimensional elementary inequality in extended-norm form. -/
theorem enorm_le_interval_sobolev_L1 {f : ℝ → E} (hf : ContDiff ℝ 1 f)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖f t‖ₑ ≤ (∫⁻ x in Icc (0 : ℝ) 1, ‖f x‖ₑ) +
      ∫⁻ x in Icc (0 : ℝ) 1, ‖deriv f x‖ₑ := by
  have h := norm_le_interval_sobolev_L1 hf (by norm_num : (0 : ℝ) < 1) ht
  simp only [sub_zero, inv_one, one_mul] at h
  have he := ENNReal.ofReal_le_ofReal h
  rw [ENNReal.ofReal_add (integral_nonneg fun _ => norm_nonneg _)
    (integral_nonneg fun _ => norm_nonneg _), ofReal_norm,
    ofReal_integral_norm_eq_lintegral_enorm hf.continuous.integrableOn_Icc.integrable,
    ofReal_integral_norm_eq_lintegral_enorm
      hf.continuous_deriv_one.integrableOn_Icc.integrable] at he
  exact he

/-- DH21 (10.5), L2428, in its iterated-integral form: smooth functions on
the unit cube are bounded by the sum of the `L¹` norms of their square-free
mixed derivatives. This is pointwise, including the boundary of the cube. -/
theorem enorm_le_cubeSobolevL1 : ∀ (n : ℕ) {f : (Fin n → ℝ) → E},
    ContDiff ℝ ∞ f → ∀ x, (∀ i, x i ∈ Icc (0 : ℝ) 1) →
      ‖f x‖ₑ ≤ cubeSobolevL1 n f := by
  intro n
  induction n with
  | zero =>
      intro f _ x _
      exact le_of_eq (congrArg (fun y => ‖f y‖ₑ) (Subsingleton.elim _ _))
  | succ n ih =>
      intro f hf x hx
      have hs := enorm_le_interval_sobolev_L1
        ((hf.comp (contDiff_cons_curve (Fin.tail x))).of_le (by simp)) (hx 0)
      simp only [Function.comp_apply, Fin.cons_self_tail] at hs
      refine hs.trans (add_le_add ?_ ?_)
      · apply lintegral_mono
        intro t
        exact ih (hf.comp (contDiff_cons_const t)) (Fin.tail x) (fun i => hx i.succ)
      · apply lintegral_mono
        intro t
        exact ih (contDiff_deriv_cons hf t) (Fin.tail x) (fun i => hx i.succ)

/-- The whole-space analogue of `cubeSobolevL1`: the sum of the integrals
of all square-free mixed derivatives, of orders at most `n`, on `ℝ^n`.
As in the cube version, the formula uses iterated Lebesgue integrals. -/
@[expose] noncomputable def wholeSobolevL1 : (n : ℕ) → ((Fin n → ℝ) → E) → ℝ≥0∞
  | 0, f => ‖f (fun i => Fin.elim0 i)‖ₑ
  | n + 1, f =>
      (∫⁻ t, wholeSobolevL1 n (fun x => f (Fin.cons t x))) +
      ∫⁻ t, wholeSobolevL1 n (fun x => deriv (fun s => f (Fin.cons s x)) t)

/-- The one-dimensional whole-space `W¹,¹` bound. -/
theorem enorm_le_whole_sobolev_L1 {f : ℝ → E} (hf : ContDiff ℝ 1 f) (t : ℝ) :
    ‖f t‖ₑ ≤ (∫⁻ x, ‖f x‖ₑ) + ∫⁻ x, ‖deriv f x‖ₑ := by
  have h := norm_le_interval_sobolev_L1 hf (by linarith : t < t + 1)
    (show t ∈ Icc t (t + 1) from ⟨le_rfl, by linarith⟩)
  simp only [add_sub_cancel_left, inv_one, one_mul] at h
  have he := ENNReal.ofReal_le_ofReal h
  rw [ENNReal.ofReal_add (integral_nonneg fun _ => norm_nonneg _)
    (integral_nonneg fun _ => norm_nonneg _), ofReal_norm,
    ofReal_integral_norm_eq_lintegral_enorm hf.continuous.integrableOn_Icc.integrable,
    ofReal_integral_norm_eq_lintegral_enorm
      hf.continuous_deriv_one.integrableOn_Icc.integrable] at he
  exact he.trans (add_le_add (lintegral_mono' Measure.restrict_le_self le_rfl)
    (lintegral_mono' Measure.restrict_le_self le_rfl))

/-- The smooth `W^{n,1}(ℝ^n) → L∞` estimate underlying TARGET
(incohproof4), L998. Only the square-free mixed derivatives are needed.
The constant is one for the displayed sum norm. -/
theorem enorm_le_wholeSobolevL1 : ∀ (n : ℕ) {f : (Fin n → ℝ) → E},
    ContDiff ℝ ∞ f → ∀ x, ‖f x‖ₑ ≤ wholeSobolevL1 n f := by
  intro n
  induction n with
  | zero =>
      intro f _ x
      exact le_of_eq (congrArg (fun y => ‖f y‖ₑ) (Subsingleton.elim _ _))
  | succ n ih =>
      intro f hf x
      have hs := enorm_le_whole_sobolev_L1
        ((hf.comp (contDiff_cons_curve (Fin.tail x))).of_le (by simp)) (x 0)
      simp only [Function.comp_apply, Fin.cons_self_tail] at hs
      refine hs.trans (add_le_add ?_ ?_)
      · apply lintegral_mono
        intro t
        exact ih (hf.comp (contDiff_cons_const t)) (Fin.tail x)
      · apply lintegral_mono
        intro t
        exact ih (contDiff_deriv_cons hf t) (Fin.tail x)

end WaveTurbulence.Analysis
