/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.SmoothPoisson
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# Vanishing of individual distant Poisson frequencies

The Riemann-Lebesgue lemma is used only to compare two finite-cutoff
conventions in the sharp Poisson limit. Quantitative tail control is
provided separately by integration by parts.
-/

public section

open MeasureTheory Set Filter
open WaveTurbulence.NumberTheory
open scoped FourierTransform Topology

namespace WaveTurbulence.VdCB

/-- Sharp interval Fourier identity, with no smooth cutoff. -/
theorem fourier_indicator_expPhase (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) (ν : ℝ) :
    𝓕 ((Ioc a b).indicator (fun x => expPhase (f x))) ν =
      ∫ x in a..b, expPhase (f x - ν * x) := by
  let A : ℝ → ℂ := (Ioc a b).indicator (fun _ => 1)
  have hA (x : ℝ) (g : ℝ → ℂ) : A x * g x = (Ioc a b).indicator g x := by
    dsimp only [A]
    by_cases hx : x ∈ Ioc a b
    · rw [indicator_of_mem hx, indicator_of_mem hx, one_mul]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]
  have hh := fourier_amplitude_expPhase A f ν
  have hleft : (fun x => A x * expPhase (f x)) = (Ioc a b).indicator (fun x => expPhase (f x)) :=
    funext fun x => hA x (fun y => expPhase (f y))
  have hright : (fun x => A x * expPhase (f x - ν * x)) =
      (Ioc a b).indicator (fun x => expPhase (f x - ν * x)) := funext fun x => hA x (fun y => expPhase (f y - ν * y))
  rw [hleft, hright] at hh
  rw [integral_indicator measurableSet_Ioc] at hh
  simpa only [intervalIntegral.integral_of_le hab] using hh

/-- Individual sharp Poisson integrals tend to zero at positive infinity. -/
theorem tendsto_integral_expPhase_sub_frequency_zero (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun ν : ℝ => ∫ x in a..b, expPhase (f x - ν * x)) atTop (𝓝 0) := by
  have hh := (Real.zero_at_infty_fourier ((Ioc a b).indicator (fun x => expPhase (f x)))).mono_left
    (atTop_le_cocompact : (atTop : Filter ℝ) ≤ cocompact ℝ)
  have heq : 𝓕 ((Ioc a b).indicator (fun x => expPhase (f x))) =
      (fun ν : ℝ => ∫ x in a..b, expPhase (f x - ν * x)) :=
    funext (fourier_indicator_expPhase f hab)
  rw [heq] at hh
  exact hh

end WaveTurbulence.VdCB
