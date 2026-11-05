/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SignedSeries
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
/-! Complex root signs commute with actual phase integrals and domain indicators. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory
open scoped ComplexConjugate

theorem zpowSign_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (sig : ℤˣ) (f : Ω → ℂ) : zpowSign sig (∫ ω, f ω ∂μ) = ∫ ω, zpowSign sig (f ω) ∂μ := by
  unfold zpowSign
  split_ifs
  · rfl
  · exact integral_conj.symm

theorem zpowSign_indicator {Ω : Type*} (sig : ℤˣ) (s : Set Ω) (f : Ω → ℂ) (ω : Ω) :
    zpowSign sig (s.indicator f ω) = s.indicator (fun ω => zpowSign sig (f ω)) ω := by
  classical
  by_cases h : ω ∈ s <;> simp [Set.indicator, h, zpowSign]

theorem zpowSign_exp_real_mul_I (sig : ℤˣ) (θ : ℝ) :
    zpowSign sig (Complex.exp ((θ : ℂ) * Complex.I)) =
      Complex.exp (((((sig : ℤ) : ℝ) * θ : ℝ) : ℂ) * Complex.I) := by
  rcases Int.units_eq_one_or sig with rfl | rfl <;>
    simp [zpowSign, map_mul, ← Complex.exp_conj]

end WaveTurbulence.Induct
