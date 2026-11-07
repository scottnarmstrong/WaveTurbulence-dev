/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.NonnegativeTimeRescale
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Signed affine rescaling of nonnegative time integrals (SUMINT-SIGNED)
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory ENNReal

namespace WaveTurbulence.SumintPar

/-- Multiplication by a sign preserves the Lebesgue integral on the line. -/
theorem lintegral_comp_sign (g : ℝ → ℝ≥0∞) {ε : ℝ} (h : ε = 1 ∨ ε = -1) :
    (∫⁻ x : ℝ, g (ε*x)) = ∫⁻ x : ℝ, g x := by
  rcases h with rfl | rfl
  · simp only [one_mul]
  · simp only [neg_mul, one_mul]
    exact (Measure.measurePreserving_neg (volume : Measure ℝ)).lintegral_comp_emb
      (MeasurableEquiv.neg ℝ).measurableEmbedding g

/-- Signed positive affine rescaling of a nonnegative real-time integral. -/
theorem lintegral_comp_affine_signed (f : ℝ → ℝ≥0∞) {c : ℝ} (hc : 0 < c) (t : ℝ) {ε : ℝ}
    (h : ε = 1 ∨ ε = -1) :
    (∫⁻ s : ℝ, f (ε*(c*(s-t)))) = ENNReal.ofReal c⁻¹ * ∫⁻ s : ℝ, f s := by
  have := lintegral_comp_affine_pos (fun u => f (ε*u)) hc t
  rw [this, lintegral_comp_sign f h]

/-- Two signed independent affine time changes have exactly the reciprocal-square scale. -/
theorem lintegral_comp_affine_two_signed (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f)
    {c : ℝ} (hc : 0 < c) (t : ℝ) {ε₀ ε₁ : ℝ} (h₀ : ε₀ = 1 ∨ ε₀ = -1) (h₁ : ε₁ = 1 ∨ ε₁ = -1) :
    (∫⁻ s : ℝ, ∫⁻ s' : ℝ, f (ε₀*(c*(s-t)), ε₁*(c*(s'-t)))) =
      ENNReal.ofReal c⁻¹ * ENNReal.ofReal c⁻¹ * ∫⁻ z : ℝ × ℝ, f z := by
  have he (s : ℝ) := lintegral_comp_affine_signed (fun u => f (ε₀*(c*(s-t)),u)) hc t h₁
  simp_rw [he]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_comp_affine_signed (fun v => ∫⁻ w : ℝ, f (v,w)) hc t h₀]
  rw [Measure.volume_eq_prod, lintegral_prod _ hf.aemeasurable]
  rw [mul_assoc]

end WaveTurbulence.SumintPar
