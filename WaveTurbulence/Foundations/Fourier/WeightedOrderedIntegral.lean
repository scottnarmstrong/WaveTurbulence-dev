/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.CutoffOrderedIntegral
public import WaveTurbulence.Foundations.Fourier.OrderedBoundaryDerivative
public import WaveTurbulence.Foundations.Fourier.TimeDerivatives
import Mathlib.Tactic

/-!
# Ordered integration with separate output cutoffs

Separate upper and lower cutoffs accommodate the derivatives of the
output cutoff without changing the source amplitudes or oscillatory phases.
-/

public section

open scoped ContDiff

namespace WaveTurbulence.Fourier

/-- An ordered integral with a separate cutoff at each output endpoint. -/
@[expose] noncomputable def weightedOrderedIntegral (n : ℕ) (a b : ℝ → ℝ)
    (A : (Fin n → ℝ) → ℂ) (t : Fin 2 → ℝ) : ℂ :=
  (a (t 0) : ℂ) * (b (t 1) : ℂ) * orderedIntegral n A (t 0) (t 1)

/-- Separate smooth cutoffs and a smooth amplitude give a smooth output. -/
theorem weightedOrderedIntegral_contDiff {n : ℕ} {a b : ℝ → ℝ} {A : (Fin n → ℝ) → ℂ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (weightedOrderedIntegral n a b A) := by
  apply ((Complex.ofRealCLM.contDiff.comp (ha.comp (by fun_prop))).mul
    (Complex.ofRealCLM.contDiff.comp (hb.comp (by fun_prop)))).mul
  exact contDiff_orderedIntegral n (hA.comp contDiff_snd) (by fun_prop) (by fun_prop)

/-- Equal output cutoffs recover the earlier literal cutoff ordered integral. -/
theorem weightedOrderedIntegral_self (n : ℕ) (χ : ℝ → ℝ) (A : (Fin n → ℝ) → ℂ) :
    weightedOrderedIntegral n χ χ A = cutoffOrderedIntegral n χ A := by
  funext t
  simp [weightedOrderedIntegral, cutoffOrderedIntegral, coordinateCutoff, Fin.prod_univ_two]

/-- Upper-time partial derivative; only the first boundary face is exposed. -/
theorem partialDeriv_weightedOrderedIntegral_upper {n : ℕ} {a b : ℝ → ℝ}
    {A : (Fin (n + 1) → ℝ) → ℂ} (ha : ContDiff ℝ ∞ a)
    (hA : ContDiff ℝ ∞ A) (t : Fin 2 → ℝ) :
    WaveTurbulence.partialDeriv 0 (weightedOrderedIntegral (n + 1) a b A) t =
      ((deriv a (t 0) : ℝ) : ℂ) * (b (t 1) : ℂ) * orderedIntegral (n + 1) A (t 0) (t 1) +
      (a (t 0) : ℂ) * (b (t 1) : ℂ) *
        orderedIntegral n (fun v => A (Fin.cons (t 0) v)) (t 0) (t 1) := by
  have ha' := ((ha.differentiable (by simp)) (t 0)).hasDerivAt.ofReal_comp
  have hb' := hasDerivAt_const (t 0) (b (t 1) : ℂ)
  have h := ((ha'.mul hb').mul (hasDerivAt_orderedIntegral_upper n hA (t 0) (t 1))).deriv
  change deriv (fun z => (a z : ℂ) * (b (t 1) : ℂ) * orderedIntegral (n + 1) A z (t 1))
    (t 0) = _ at h
  simp only [Pi.mul_apply] at h
  simpa only [WaveTurbulence.partialDeriv, weightedOrderedIntegral, Function.update_self,
    Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), mul_zero, add_zero] using h

/-- Lower-time partial derivative; only the last boundary face is exposed. -/
theorem partialDeriv_weightedOrderedIntegral_lower {n : ℕ} {a b : ℝ → ℝ}
    {A : (Fin (n + 1) → ℝ) → ℂ} (hb : ContDiff ℝ ∞ b)
    (hA : ContDiff ℝ ∞ A) (t : Fin 2 → ℝ) :
    WaveTurbulence.partialDeriv 1 (weightedOrderedIntegral (n + 1) a b A) t =
      (a (t 0) : ℂ) * ((deriv b (t 1) : ℝ) : ℂ) * orderedIntegral (n + 1) A (t 0) (t 1) -
      (a (t 0) : ℂ) * (b (t 1) : ℂ) *
        orderedIntegral n (fun v => A (Fin.snoc v (t 1))) (t 0) (t 1) := by
  have ha' := hasDerivAt_const (t 1) (a (t 0) : ℂ)
  have hb' := ((hb.differentiable (by simp)) (t 1)).hasDerivAt.ofReal_comp
  have h := ((ha'.mul hb').mul (hasDerivAt_orderedIntegral_lower n hA (t 0) (t 1))).deriv
  change deriv (fun z => (a (t 0) : ℂ) * (b z : ℂ) * orderedIntegral (n + 1) A (t 0) z)
    (t 1) = _ at h
  simp only [Pi.mul_apply, zero_mul, zero_add, mul_neg, ← sub_eq_add_neg] at h
  simpa only [WaveTurbulence.partialDeriv, weightedOrderedIntegral, Function.update_self,
    Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide)] using h

end WaveTurbulence.Fourier
