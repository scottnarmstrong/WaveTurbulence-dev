/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.OrderedBoundaryDerivative
public import WaveTurbulence.Frozen.Defs.PartialDeriv
import Mathlib.Tactic

/-!
# Mixed endpoint derivatives of ordered integrals

The frozen coordinate partial derivatives remove the first and last
boundary faces. The amplitude itself is not differentiated, so no phase
frequency occurs in this identity.
-/

public section

open scoped ContDiff

namespace WaveTurbulence.Fourier

/-- Frozen lower-time partial derivative of an ordered integral. -/
theorem partialDeriv_orderedIntegral_lower {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (t : Fin 2 → ℝ) :
    WaveTurbulence.partialDeriv 1 (fun z => orderedIntegral (n + 1) F (z 0) (z 1)) t =
      -orderedIntegral n (fun v => F (Fin.snoc v (t 1))) (t 0) (t 1) := by
  simp only [WaveTurbulence.partialDeriv, Function.update_self,
    Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
  exact (hasDerivAt_orderedIntegral_lower n hF (t 0) (t 1)).deriv

/-- Frozen upper-time partial derivative of an ordered integral. -/
theorem partialDeriv_orderedIntegral_upper {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (t : Fin 2 → ℝ) :
    WaveTurbulence.partialDeriv 0 (fun z => orderedIntegral (n + 1) F (z 0) (z 1)) t =
      orderedIntegral n (fun v => F (Fin.cons (t 0) v)) (t 0) (t 1) := by
  simp only [WaveTurbulence.partialDeriv, Function.update_self,
    Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
  exact (hasDerivAt_orderedIntegral_upper n hF (t 0) (t 1)).deriv

/-- The mixed endpoint derivative removes both end faces, with a minus sign. -/
theorem partialDeriv_orderedIntegral_mixed {n : ℕ} {F : (Fin (n + 2) → ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (t : Fin 2 → ℝ) :
    WaveTurbulence.partialDeriv 0
      (WaveTurbulence.partialDeriv 1 (fun z => orderedIntegral (n + 2) F (z 0) (z 1))) t =
      -orderedIntegral n (fun v => F (Fin.snoc (Fin.cons (t 0) v) (t 1))) (t 0) (t 1) := by
  have he : WaveTurbulence.partialDeriv 1 (fun z : Fin 2 → ℝ =>
      orderedIntegral (n + 2) F (z 0) (z 1)) =
      fun z => -orderedIntegral (n + 1) (fun v => F (Fin.snoc v (z 1))) (z 0) (z 1) := by
    funext z
    exact partialDeriv_orderedIntegral_lower hF z
  rw [he]
  simp only [WaveTurbulence.partialDeriv, Function.update_self,
    Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
  have hs : ContDiff ℝ ∞ (fun v : Fin (n + 1) → ℝ => F (Fin.snoc v (t 1))) := by
    apply hF.comp
    apply contDiff_pi.mpr
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last]; exact contDiff_const
    · simp only [Fin.snoc_castSucc]; fun_prop
  exact (hasDerivAt_orderedIntegral_upper n hs (t 0) (t 1)).neg.deriv

end WaveTurbulence.Fourier
