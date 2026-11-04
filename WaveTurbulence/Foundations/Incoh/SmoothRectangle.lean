/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SmoothStepMass
public import WaveTurbulence.Foundations.Fourier.TimeIntegralOperators
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Smooth rectangular fibers and their mixed derivative

The interval derivative mass bound tensorizes without dependence on the
endpoints or the smoothing width, as required by TARGET (incohproof27).
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace WaveTurbulence.Incoh

/-- The tensor product of the two interval windows. -/
@[expose] def smoothRectangle (ε : ℝ) (a b t : Fin 2 → ℝ) : ℂ :=
  (smoothInterval ε (a 0) (b 0) (t 0) : ℂ) * smoothInterval ε (a 1) (b 1) (t 1)

@[fun_prop] theorem contDiff_smoothRectangle (ε : ℝ) (a b : Fin 2 → ℝ) :
    ContDiff ℝ ∞ (smoothRectangle ε a b) := by
  unfold smoothRectangle
  exact (Complex.ofRealCLM.contDiff.comp ((contDiff_smoothInterval ε (a 0) (b 0)).comp
    (by fun_prop))).mul
    (Complex.ofRealCLM.contDiff.comp ((contDiff_smoothInterval ε (a 1) (b 1)).comp (by fun_prop)))

theorem hasCompactSupport_smoothRectangle {ε : ℝ} (hε : 0 < ε)
    (a b : Fin 2 → ℝ) (hab : a ≤ b) : HasCompactSupport (smoothRectangle ε a b) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := a) (b := fun j => b j + ε))
  intro t ht
  have hx : ∃ j, ¬ (a j ≤ t j ∧ t j ≤ b j + ε) := by
    by_contra hn
    apply ht
    push Not at hn
    exact ⟨fun j => (hn j).1, fun j => (hn j).2⟩
  obtain ⟨j, hj⟩ := hx
  have hz : smoothInterval ε (a j) (b j) (t j) = 0 := by
    rcases not_and_or.mp hj with ha | hb
    · exact smoothInterval_eq_zero_of_le hε (hab j) (le_of_not_ge ha)
    · exact smoothInterval_eq_zero_of_ge hε (hab j) (le_of_not_ge hb)
  fin_cases j
  · change smoothInterval ε (a 0) (b 0) (t 0) = 0 at hz
    simp only [smoothRectangle, hz, Complex.ofReal_zero, zero_mul]
  · change smoothInterval ε (a 1) (b 1) (t 1) = 0 at hz
    simp only [smoothRectangle, hz, Complex.ofReal_zero, mul_zero]

/-- The frozen coordinate derivative computes the expected tensor derivative. -/
theorem mixedTimePartial_tensor {f g : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (t : Fin 2 → ℝ) :
    Fourier.mixedTimePartial (fun u => (f (u 0) : ℂ) * g (u 1)) t =
      ((deriv f (t 0) : ℝ) : ℂ) * deriv g (t 1) := by
  have h1 (u : Fin 2 → ℝ) :
      WaveTurbulence.partialDeriv 1 (fun v => (f (v 0) : ℂ) * g (v 1)) u =
        (f (u 0) : ℂ) * deriv g (u 1) := by
    unfold WaveTurbulence.partialDeriv
    simp only [Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1), Function.update_self]
    exact ((hg (u 1)).hasDerivAt.ofReal_comp.const_mul _).deriv
  unfold Fourier.mixedTimePartial
  rw [show WaveTurbulence.partialDeriv 1 (fun v => (f (v 0) : ℂ) * g (v 1)) =
      (fun u => (f (u 0) : ℂ) * deriv g (u 1)) from funext h1]
  unfold WaveTurbulence.partialDeriv
  simp only [Function.update_self, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
  exact ((hf (t 0)).hasDerivAt.ofReal_comp.mul_const _).deriv

theorem mixedTimePartial_smoothRectangle (ε : ℝ) (a b t : Fin 2 → ℝ) :
    Fourier.mixedTimePartial (smoothRectangle ε a b) t =
      ((deriv (smoothInterval ε (a 0) (b 0)) (t 0) : ℝ) : ℂ) *
        deriv (smoothInterval ε (a 1) (b 1)) (t 1) :=
  mixedTimePartial_tensor ((contDiff_smoothInterval ε (a 0) (b 0)).differentiable (by norm_num))
    ((contDiff_smoothInterval ε (a 1) (b 1)).differentiable (by norm_num)) t

end WaveTurbulence.Incoh
