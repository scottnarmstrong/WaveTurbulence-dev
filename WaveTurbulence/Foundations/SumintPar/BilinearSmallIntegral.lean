/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.BilinearWeylBridge
public import WaveTurbulence.Foundations.WeylSums.BilinearPointwise
import Mathlib.Tactic

/-!
# Integrating the small bilinear time region

The bound includes a first-moment weight. Thus the same fixed constant
controls the ordinary small-time contribution and the endpoint-strip
contributions used for bad and incoherent blocks.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set

namespace WaveTurbulence.SumintPar

/-- Integrable pointwise majorant on the whole real line. -/
theorem pair_kernel_mass_nonneg (d : ℕ) :
    0 ≤ ∫ s : ℝ, (1 + |s|) / scalarBracket s^d :=
  integral_nonneg (fun s => div_nonneg (by positivity)
    (pow_nonneg (zero_le_one.trans (one_le_scalarBracket s)) _))

/-- First-moment small-time estimate for the literal source bilinear lattice sum. -/
theorem exists_bilinear_small_integral_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L : ℝ}, 1 ≤ L → ∀ a b ξ ζ : Mom d,
      (∫ s in {s : ℝ | |s| ≤ L}, (1+|s|) *
        ‖WeylSums.bilinearLatticeSum L s a b ξ ζ‖) ≤ C * L^(2*d) := by
  obtain ⟨C, hC, hb⟩ := exists_bilinear_weyl_small_bound d
  refine ⟨C * ∫ s : ℝ, (1+|s|)/scalarBracket s^d,
    mul_nonneg hC (pair_kernel_mass_nonneg d), ?_⟩
  intro L hL a b ξ ζ
  have hLp : 0 < L := by linarith
  let S := {s : ℝ | |s| ≤ L}
  have hS : MeasurableSet S := isClosed_le (by fun_prop) continuous_const |>.measurableSet
  have hcont : Continuous (fun s : ℝ => (1+|s|) *
      ‖WeylSums.bilinearLatticeSum L s a b ξ ζ‖) :=
    (continuous_const.add continuous_abs).mul
      (WeylSums.continuous_bilinearLatticeSum hLp a b ξ ζ).norm
  have hker := (integrable_first_moment_kernel hd).const_mul (C * L^(2*d))
  have hmajor (s : ℝ) (hs : s ∈ S) :
      (1+|s|) * ‖WeylSums.bilinearLatticeSum L s a b ξ ζ‖ ≤
        (C * L^(2*d)) * ((1+|s|)/scalarBracket s^d) := by
    exact (mul_le_mul_of_nonneg_left (hb hL s hs a b ξ ζ) (by positivity)).trans_eq (by ring)
  have hint : IntegrableOn (fun s : ℝ => (1+|s|) *
      ‖WeylSums.bilinearLatticeSum L s a b ξ ζ‖) S := by
    apply hker.integrableOn.mono' hcont.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem hS] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (norm_nonneg _))]
    exact hmajor s hs
  calc
    _ ≤ ∫ s in S, (C * L^(2*d)) * ((1+|s|)/scalarBracket s^d) :=
      setIntegral_mono_on hint hker.integrableOn hS hmajor
    _ ≤ ∫ s : ℝ, (C * L^(2*d)) * ((1+|s|)/scalarBracket s^d) := by
      apply setIntegral_le_integral hker
      apply ae_of_all
      intro s
      exact mul_nonneg (mul_nonneg hC (pow_nonneg hLp.le _))
        (div_nonneg (by positivity) (pow_nonneg (zero_le_one.trans (one_le_scalarBracket s)) _))
    _ = _ := by rw [integral_const_mul]; ring

end WaveTurbulence.SumintPar
