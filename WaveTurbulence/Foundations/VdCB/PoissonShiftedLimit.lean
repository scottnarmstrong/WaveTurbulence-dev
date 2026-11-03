/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.PoissonSymmetricLimit
public import WaveTurbulence.Foundations.VdCB.FrequencyLimit
public import WaveTurbulence.Foundations.VdCB.FrequencyPartition

/-!
# Shifted sharp Poisson cutoffs

Changing the center of a finite Poisson cutoff by a fixed integer does
not change its limit. The correction is a fixed finite number of Fourier
integrals, each tending to zero.
-/

public section

open MeasureTheory Set Filter
open WaveTurbulence.NumberTheory
open scoped Topology

namespace WaveTurbulence.VdCB

private theorem sum_symmetric_frequency_sign (f : ℝ → ℝ) (a b : ℝ) (K : ℕ) :
    (∑ ν ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ∫ x in a..b, expPhase (f x - (ν : ℝ) * x)) =
      ∑ ν ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ∫ x in a..b, expPhase ((ν : ℝ) * x) * expPhase (f x) := by
  apply Finset.sum_equiv (Equiv.neg ℤ)
  · intro ν
    simp only [Finset.mem_Icc, Equiv.neg_apply]
    omega
  · intro ν _
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    rw [← expPhase_add]
    congr 1
    simp only [Equiv.neg_apply, Int.cast_neg]
    ring

/-- Sharp Poisson limit with equal cutoffs outside `[0,N]`. -/
theorem poisson_shifted_limit {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {a b : ℕ} (hab : a ≤ b) (N : ℕ) :
    Tendsto (fun K : ℕ => ∑ ν ∈ Finset.Icc (-(K : ℤ)) ((N : ℤ) + K),
      ∫ x in (a : ℝ)..b, expPhase (f x - (ν : ℝ) * x)) atTop
      (𝓝 ((∑ n ∈ Finset.Ico a b, expPhase (f ((n : ℝ) + 1))) -
        (expPhase (f b) - expPhase (f a)) / 2)) := by
  have hsym := poisson_symmetric_limit ((contDiff_expPhase 1).comp hf) hab
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hext : Tendsto (fun K : ℕ => ∑ j ∈ Finset.range N,
      ∫ x in (a : ℝ)..b, expPhase (f x - (((K : ℤ) + j + 1 : ℤ) : ℝ) * x)) atTop (𝓝 0) := by
    have hh := tendsto_finsetSum (Finset.range N) (fun j _ =>
      (tendsto_integral_expPhase_sub_frequency_zero f habR).comp
        (tendsto_atTop_add_const_right atTop ((j : ℝ) + 1)
          (tendsto_natCast_atTop_atTop (R := ℝ))))
    simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one, add_assoc, Finset.sum_const_zero, Function.comp_apply] using hh
  have hh := hsym.add hext
  simpa only [sum_extended_frequency_interval, sum_symmetric_frequency_sign, add_zero, Function.comp_apply] using hh

end WaveTurbulence.VdCB
