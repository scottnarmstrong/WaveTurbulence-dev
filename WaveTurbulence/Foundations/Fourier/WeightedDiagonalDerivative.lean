/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.WeightedOrderedIntegral
public import WaveTurbulence.Foundations.Fourier.OrderedDiagonalDerivative
public import WaveTurbulence.Foundations.Fourier.DirectionalFourierMoments
import Mathlib.Tactic

/-!
# Diagonal differentiation of cutoff ordered integrals

The derivative splits into the two output-cutoff terms and the translated
amplitude term. Balanced oscillatory phases are constant in the last term.
-/

public section

open scoped ContDiff

namespace WaveTurbulence.Fourier

/-- Simultaneous time translation differentiates only the cutoffs and the diagonal amplitude. -/
theorem timeDirectionalDerivative_weightedOrderedIntegral {n : ℕ} {a b : ℝ → ℝ}
    {A : (Fin n → ℝ) → ℂ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hA : ContDiff ℝ ∞ A) (t : Fin 2 → ℝ) :
    timeDirectionalDerivative (fun _ => 1) (weightedOrderedIntegral n a b A) t =
      weightedOrderedIntegral n (deriv a) b A t +
      weightedOrderedIntegral n a (deriv b) A t +
      weightedOrderedIntegral n a b (fun v => fderiv ℝ A v (fun _ => 1)) t := by
  have ha0 : HasDerivAt (fun c : ℝ => a (t 0 + c)) (deriv a (t 0)) 0 := by
    simpa only [Function.comp_def, add_zero, mul_one] using
      (((ha.differentiable (by simp)) (t 0 + (0 : ℝ))).hasDerivAt.comp 0
        ((hasDerivAt_id (0 : ℝ)).const_add (t 0)))
  have hb0 : HasDerivAt (fun c : ℝ => b (t 1 + c)) (deriv b (t 1)) 0 := by
    simpa only [Function.comp_def, add_zero, mul_one] using
      (((hb.differentiable (by simp)) (t 1 + (0 : ℝ))).hasDerivAt.comp 0
        ((hasDerivAt_id (0 : ℝ)).const_add (t 1)))
  have hp := ((ha0.ofReal_comp.mul hb0.ofReal_comp).mul
    (hasDerivAt_orderedIntegral_diagonal hA (t 0) (t 1)))
  have hreg := weightedOrderedIntegral_contDiff ha hb hA
  have ht : HasDerivAt (fun c : ℝ => fun j : Fin 2 => t j + c) (fun _ => 1) 0 := by
    apply hasDerivAt_pi.mpr
    intro j
    exact (hasDerivAt_id (0 : ℝ)).const_add (t j)
  have hd := (hreg.differentiable (by simp) (fun j => t j + (0 : ℝ))).hasFDerivAt.comp_hasDerivAt 0 ht
  have he := hd.unique hp
  simp only [add_zero, Pi.mul_apply] at he
  change timeDirectionalDerivative (fun _ => 1) (weightedOrderedIntegral n a b A) t = _ at he
  calc
    _ = _ := he
    _ = _ := by
      simp only [weightedOrderedIntegral]
      ring

end WaveTurbulence.Fourier
