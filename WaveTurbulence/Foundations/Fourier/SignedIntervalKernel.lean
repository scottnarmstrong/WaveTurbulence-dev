/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.OrderedBoxBound
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Bounded kernels for oriented interval integration

The kernel has magnitude at most one and is jointly measurable in both
endpoints and the integration variable. It gives a literal integral
representation, including reversed endpoints.
-/

public section

open MeasureTheory Set

namespace WaveTurbulence.Fourier

/-- The signed characteristic function of an oriented interval. -/
@[expose] noncomputable def signedIntervalKernel (s t u : ℝ) : ℂ :=
  (Ioc s t).indicator (fun _ => (1 : ℂ)) u -
    (Ioc t s).indicator (fun _ => (1 : ℂ)) u

/-- The two nonzero pieces of the signed kernel are disjoint. -/
theorem norm_signedIntervalKernel_le (s t u : ℝ) : ‖signedIntervalKernel s t u‖ ≤ 1 := by
  unfold signedIntervalKernel
  by_cases h1 : u ∈ Ioc s t <;> by_cases h2 : u ∈ Ioc t s
  · have hh := h1.1.trans_le h1.2
    have hh' := h2.1.trans_le h2.2
    linarith
  · simp [indicator_of_mem h1, indicator_of_notMem h2]
  · simp [indicator_of_notMem h1, indicator_of_mem h2]
  · simp [indicator_of_notMem h1, indicator_of_notMem h2]

/-- Joint measurability in the two endpoints and the integration variable. -/
theorem signedIntervalKernel_measurable :
    Measurable (fun p : (ℝ × ℝ) × ℝ => signedIntervalKernel p.1.1 p.1.2 p.2) := by
  classical
  have h1 : MeasurableSet {p : (ℝ × ℝ) × ℝ | p.1.1 < p.2 ∧ p.2 ≤ p.1.2} :=
    (measurableSet_lt (f := fun p : (ℝ × ℝ) × ℝ => p.1.1)
      (g := fun p => p.2) (by fun_prop) (by fun_prop)).inter
      (measurableSet_le (f := fun p : (ℝ × ℝ) × ℝ => p.2)
        (g := fun p => p.1.2) (by fun_prop) (by fun_prop))
  have h2 : MeasurableSet {p : (ℝ × ℝ) × ℝ | p.1.2 < p.2 ∧ p.2 ≤ p.1.1} :=
    (measurableSet_lt (f := fun p : (ℝ × ℝ) × ℝ => p.1.2)
      (g := fun p => p.2) (by fun_prop) (by fun_prop)).inter
      (measurableSet_le (f := fun p : (ℝ × ℝ) × ℝ => p.2)
        (g := fun p => p.1.1) (by fun_prop) (by fun_prop))
  have hf1 : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      if p.1.1 < p.2 ∧ p.2 ≤ p.1.2 then (1 : ℂ) else 0) :=
    Measurable.ite h1 measurable_const measurable_const
  have hf2 : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      if p.1.2 < p.2 ∧ p.2 ≤ p.1.1 then (1 : ℂ) else 0) :=
    Measurable.ite h2 measurable_const measurable_const
  convert hf1.sub hf2 using 1
  funext p
  simp only [signedIntervalKernel, Set.indicator, Set.mem_Ioc, Pi.sub_apply]

/-- The kernel representation is literal even for inputs with nonintegrable slices. -/
theorem integral_signedIntervalKernel_mul (f : ℝ → ℂ) (s t : ℝ) :
    (∫ u, signedIntervalKernel s t u * f u) = ∫ u in s..t, f u := by
  rcases le_total s t with hst | hts
  · have he : (fun u => signedIntervalKernel s t u * f u) = (Ioc s t).indicator f := by
      funext u
      have hr : Ioc t s = ∅ := Ioc_eq_empty_of_le hst
      simp only [signedIntervalKernel, hr, indicator_empty, sub_zero]
      by_cases hu : u ∈ Ioc s t <;> simp [hu]
    rw [he, integral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le hst]
  · have he : (fun u => signedIntervalKernel s t u * f u) =
        fun u => -(Ioc t s).indicator f u := by
      funext u
      have hr : Ioc s t = ∅ := Ioc_eq_empty_of_le hts
      simp only [signedIntervalKernel, hr, indicator_empty, zero_sub]
      by_cases hu : u ∈ Ioc t s <;> simp [hu]
    rw [he, integral_neg, integral_indicator measurableSet_Ioc, intervalIntegral.integral_of_ge hts]

end WaveTurbulence.Fourier
