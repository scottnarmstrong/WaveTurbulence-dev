/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LemLin.ScalarPoisson
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Scalar amplitudes for the cubic estimate

Smooth scalar amplitudes supported in the fixed unit interval are closed
under the operations appearing in integration by parts. The actual fixed
cutoff is included, so the auxiliary amplitude class adds no source premises.
-/

public section

namespace WaveTurbulence.LemLin
open MeasureTheory Set
open scoped ContDiff SchwartzMap

/-- Smooth amplitudes with fixed compact support, used only as proof data. -/
structure ScalarCutoff where
  toFun : ℝ → ℂ
  smooth : ContDiff ℝ ∞ toFun
  support_subset : tsupport toFun ⊆ Icc (-1) 1

instance : CoeFun ScalarCutoff (fun _ => ℝ → ℂ) := ⟨ScalarCutoff.toFun⟩

namespace ScalarCutoff

theorem hasCompactSupport (f : ScalarCutoff) : HasCompactSupport (f : ℝ → ℂ) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) f.support_subset

@[expose] noncomputable def schwartz (f : ScalarCutoff) : 𝓢(ℝ, ℂ) :=
  f.hasCompactSupport.toSchwartzMap f.smooth

@[simp] theorem schwartz_apply (f : ScalarCutoff) (x : ℝ) : f.schwartz x = f x := rfl

theorem integrable (f : ScalarCutoff) : Integrable (f : ℝ → ℂ) :=
  f.smooth.continuous.integrable_of_hasCompactSupport f.hasCompactSupport

/-- Differentiation preserves the amplitude class. -/
@[expose] noncomputable def differentiate (f : ScalarCutoff) : ScalarCutoff where
  toFun := deriv (f : ℝ → ℂ)
  smooth := (contDiff_infty_iff_deriv.mp f.smooth).2
  support_subset := tsupport_deriv_subset.trans f.support_subset

/-- Multiplication by the coordinate preserves fixed support. -/
@[expose] noncomputable def mulCoordinate (f : ScalarCutoff) : ScalarCutoff where
  toFun := fun x => (x : ℂ) * f x
  smooth := Complex.ofRealCLM.contDiff.mul f.smooth
  support_subset := tsupport_mul_subset_right.trans f.support_subset

end ScalarCutoff

/-- The cutoff from the pinned source belongs to the auxiliary amplitude class. -/
@[expose] noncomputable def fixedScalarCutoff : ScalarCutoff where
  toFun := Fourier.chi0Complex
  smooth := Fourier.chi0Complex_contDiff
  support_subset := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra h
    have hlarge : 1 ≤ |x| := by
      have hx' : ¬ (-1 ≤ x ∧ x ≤ 1) := h
      rcases lt_or_ge x (-1) with hl | hl
      · rw [abs_of_neg (by linarith)]
        linarith
      · have hu : 1 < x := lt_of_not_ge (fun hu => hx' ⟨hl, hu⟩)
        exact hu.le.trans (le_abs_self x)
    exact hx (by simp only [Fourier.chi0Complex, Fourier.chi0_eq_zero hlarge, Complex.ofReal_zero])

end WaveTurbulence.LemLin
