/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.WeightedOrderedIntegral
import Mathlib.Tactic

/-!
# Mixed boundary derivatives with separate output cutoffs

The four product-rule terms expose the two boundary faces and the
corresponding cutoff derivatives. No derivative of the amplitude occurs.
-/

public section

open scoped ContDiff

namespace WaveTurbulence.Fourier

/-- The mixed time derivative of the weighted ordered integral. -/
theorem partialDeriv_weightedOrderedIntegral_mixed {n : ℕ} {a b : ℝ → ℝ}
    {A : (Fin (n + 2) → ℝ) → ℂ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hA : ContDiff ℝ ∞ A) (t : Fin 2 → ℝ) :
    WaveTurbulence.partialDeriv 0
      (WaveTurbulence.partialDeriv 1 (weightedOrderedIntegral (n + 2) a b A)) t =
      ((deriv a (t 0) : ℝ) : ℂ) * ((deriv b (t 1) : ℝ) : ℂ) *
        orderedIntegral (n + 2) A (t 0) (t 1) +
      (a (t 0) : ℂ) * ((deriv b (t 1) : ℝ) : ℂ) *
        orderedIntegral (n + 1) (fun v => A (Fin.cons (t 0) v)) (t 0) (t 1) -
      ((deriv a (t 0) : ℝ) : ℂ) * (b (t 1) : ℂ) *
        orderedIntegral (n + 1) (fun v => A (Fin.snoc v (t 1))) (t 0) (t 1) -
      (a (t 0) : ℂ) * (b (t 1) : ℂ) *
        orderedIntegral n (fun v => A (Fin.snoc (Fin.cons (t 0) v) (t 1))) (t 0) (t 1) := by
  have he : WaveTurbulence.partialDeriv 1 (weightedOrderedIntegral (n + 2) a b A) =
      fun z => (a (z 0) : ℂ) * ((deriv b (z 1) : ℝ) : ℂ) *
        orderedIntegral (n + 2) A (z 0) (z 1) -
        (a (z 0) : ℂ) * (b (z 1) : ℂ) *
          orderedIntegral (n + 1) (fun v => A (Fin.snoc v (z 1))) (z 0) (z 1) := by
    funext z
    exact partialDeriv_weightedOrderedIntegral_lower hb hA z
  have hAs : ContDiff ℝ ∞ (fun v : Fin (n + 1) → ℝ => A (Fin.snoc v (t 1))) := by
    apply hA.comp
    apply contDiff_pi.mpr
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last]; exact contDiff_const
    · simp only [Fin.snoc_castSucc]; fun_prop
  have ha' := ((ha.differentiable (by simp)) (t 0)).hasDerivAt.ofReal_comp
  have hfirst := (ha'.mul (hasDerivAt_const (t 0) ((deriv b (t 1) : ℝ) : ℂ))).mul
    (hasDerivAt_orderedIntegral_upper (n + 1) hA (t 0) (t 1))
  have hsecond := (ha'.mul (hasDerivAt_const (t 0) (b (t 1) : ℂ))).mul
    (hasDerivAt_orderedIntegral_upper n hAs (t 0) (t 1))
  have hd := (hfirst.sub hsecond).deriv
  change deriv (fun z => (a z : ℂ) * ((deriv b (t 1) : ℝ) : ℂ) *
      orderedIntegral (n + 2) A z (t 1) - (a z : ℂ) * (b (t 1) : ℂ) *
      orderedIntegral (n + 1) (fun v => A (Fin.snoc v (t 1))) z (t 1)) (t 0) = _ at hd
  simp only [Pi.mul_apply, mul_zero, add_zero, sub_add_eq_sub_sub] at hd
  rw [he]
  simpa only [WaveTurbulence.partialDeriv, Function.update_self,
    Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)] using hd

end WaveTurbulence.Fourier
