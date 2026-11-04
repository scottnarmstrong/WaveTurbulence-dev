/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.FourMomentLinearity
public import WaveTurbulence.Foundations.Fourier.OrderedFaceRegularity
import Mathlib.Tactic

/-!
# Endpoint product rules for the frozen coordinate derivatives

These identities apply to any smooth two-time function, independently of
the integral representation used to construct it.
-/

public section

open scoped ContDiff

namespace WaveTurbulence.Fourier

/-- Differentiation in the first endpoint of a separately cut off function. -/
theorem partialDeriv_endpoint_product_zero {a b : ℝ → ℝ} {G : (Fin 2 → ℝ) → ℂ}
    (ha : ContDiff ℝ ∞ a) (hG : ContDiff ℝ ∞ G) (t : Fin 2 → ℝ) :
    WaveTurbulence.partialDeriv 0 (fun z => (a (z 0) : ℂ) * (b (z 1) : ℂ) * G z) t =
      ((deriv a (t 0) : ℝ) : ℂ) * (b (t 1) : ℂ) * G t +
        (a (t 0) : ℂ) * (b (t 1) : ℂ) * WaveTurbulence.partialDeriv 0 G t := by
  have hg : DifferentiableAt ℝ (fun z => G (Function.update t 0 z)) (t 0) :=
    (hG.differentiable (by simp) _).comp _ (hasDerivAt_update t 0 (t 0)).differentiableAt
  have hd := ((((ha.differentiable (by simp)) (t 0)).hasDerivAt.ofReal_comp).mul
    (hasDerivAt_const (t 0) (b (t 1) : ℂ))).mul hg.hasDerivAt
  change HasDerivAt (fun z => (a z : ℂ) * (b (t 1) : ℂ) * G (Function.update t 0 z)) _ _ at hd
  simpa only [WaveTurbulence.partialDeriv, Function.update_self,
    Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), Function.update_eq_self,
    Pi.mul_apply, mul_zero, add_zero] using hd.deriv

/-- Differentiation in the second endpoint of a separately cut off function. -/
theorem partialDeriv_endpoint_product_one {a b : ℝ → ℝ} {G : (Fin 2 → ℝ) → ℂ}
    (hb : ContDiff ℝ ∞ b) (hG : ContDiff ℝ ∞ G) (t : Fin 2 → ℝ) :
    WaveTurbulence.partialDeriv 1 (fun z => (a (z 0) : ℂ) * (b (z 1) : ℂ) * G z) t =
      (a (t 0) : ℂ) * ((deriv b (t 1) : ℝ) : ℂ) * G t +
        (a (t 0) : ℂ) * (b (t 1) : ℂ) * WaveTurbulence.partialDeriv 1 G t := by
  have hg : DifferentiableAt ℝ (fun z => G (Function.update t 1 z)) (t 1) :=
    (hG.differentiable (by simp) _).comp _ (hasDerivAt_update t 1 (t 1)).differentiableAt
  have hd := ((hasDerivAt_const (t 1) (a (t 0) : ℂ)).mul
    (((hb.differentiable (by simp)) (t 1)).hasDerivAt.ofReal_comp)).mul hg.hasDerivAt
  change HasDerivAt (fun z => (a (t 0) : ℂ) * (b z : ℂ) * G (Function.update t 1 z)) _ _ at hd
  simpa only [WaveTurbulence.partialDeriv, Function.update_self,
    Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), Function.update_eq_self,
    Pi.mul_apply, zero_mul, zero_add] using hd.deriv

/-- The mixed derivative consists of the four square-free product terms. -/
theorem partialDeriv_endpoint_product_mixed {a b : ℝ → ℝ} {G : (Fin 2 → ℝ) → ℂ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hG : ContDiff ℝ ∞ G)
    (t : Fin 2 → ℝ) :
    WaveTurbulence.partialDeriv 0 (WaveTurbulence.partialDeriv 1
      (fun z => (a (z 0) : ℂ) * (b (z 1) : ℂ) * G z)) t =
      ((deriv a (t 0) : ℝ) : ℂ) * ((deriv b (t 1) : ℝ) : ℂ) * G t +
      (a (t 0) : ℂ) * ((deriv b (t 1) : ℝ) : ℂ) * WaveTurbulence.partialDeriv 0 G t +
      ((deriv a (t 0) : ℝ) : ℂ) * (b (t 1) : ℂ) * WaveTurbulence.partialDeriv 1 G t +
      (a (t 0) : ℂ) * (b (t 1) : ℂ) *
        WaveTurbulence.partialDeriv 0 (WaveTurbulence.partialDeriv 1 G) t := by
  let T₀ := fun z : Fin 2 → ℝ => (a (z 0) : ℂ) * ((deriv b (z 1) : ℝ) : ℂ) * G z
  let T₁ := fun z : Fin 2 → ℝ => (a (z 0) : ℂ) * (b (z 1) : ℂ) * WaveTurbulence.partialDeriv 1 G z
  have hdb : ContDiff ℝ ∞ (deriv b) := (contDiff_infty_iff_deriv.mp hb).2
  have hG1 := WaveTurbulence.contDiff_infty_partialDeriv hG 1
  have hT₀ : ContDiff ℝ ∞ T₀ := endpoint_product_contDiff ha hdb hG
  have hT₁ : ContDiff ℝ ∞ T₁ := endpoint_product_contDiff ha hb hG1
  have he : WaveTurbulence.partialDeriv 1
      (fun z => (a (z 0) : ℂ) * (b (z 1) : ℂ) * G z) = T₀ + T₁ :=
    funext (partialDeriv_endpoint_product_one hb hG)
  rw [he]
  change WaveTurbulence.partialDeriv 0 (fun z => T₀ z + T₁ z) t = _
  rw [partialDeriv_add_smooth hT₀ hT₁]
  change WaveTurbulence.partialDeriv 0 T₀ t + WaveTurbulence.partialDeriv 0 T₁ t = _
  rw [partialDeriv_endpoint_product_zero ha hG,
    partialDeriv_endpoint_product_zero ha hG1]
  ring

end WaveTurbulence.Fourier
