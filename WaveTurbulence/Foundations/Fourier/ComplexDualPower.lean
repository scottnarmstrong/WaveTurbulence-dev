/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic

/-!
# Complex dual powers

The dual test function for the `Lᵖ` norm is the conjugate phase times the
appropriate magnitude power. Its product with the original function is
real and nonnegative, so no cancellation enters the duality argument.
-/

public section

open scoped ComplexConjugate

namespace WaveTurbulence.Fourier

/-- The unnormalized dual power used to test an `L^q` norm. -/
@[expose] noncomputable def complexDualPower (q : ℝ) (z : ℂ) : ℂ :=
  conj z * (‖z‖ ^ (q - 2) : ℝ)

@[fun_prop] theorem complexDualPower_measurable (q : ℝ) : Measurable (complexDualPower q) := by
  unfold complexDualPower
  fun_prop

/-- The dual power has magnitude `|z|^{q-1}`. -/
theorem norm_complexDualPower {q : ℝ} (hq : 1 < q) (z : ℂ) :
    ‖complexDualPower q z‖ = ‖z‖ ^ (q - 1) := by
  by_cases hz : z = 0
  · simp [complexDualPower, hz, Real.zero_rpow (by linarith : q - 1 ≠ 0)]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [complexDualPower, norm_mul, Complex.norm_conj, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg hn.le _)]
  calc
    ‖z‖ * ‖z‖ ^ (q - 2) = ‖z‖ ^ (1 : ℝ) * ‖z‖ ^ (q - 2) := by rw [Real.rpow_one]
    _ = ‖z‖ ^ (1 + (q - 2)) := (Real.rpow_add hn _ _).symm
    _ = ‖z‖ ^ (q - 1) := by congr 1; ring

/-- Pairing with the dual power gives the `q`-th power of the magnitude. -/
theorem mul_complexDualPower {q : ℝ} (hq : 1 < q) (z : ℂ) :
    z * complexDualPower q z = (‖z‖ ^ q : ℝ) := by
  by_cases hz : z = 0
  · simp [complexDualPower, hz, Real.zero_rpow (by linarith : q ≠ 0)]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [complexDualPower, ← mul_assoc, mul_comm z (conj z), Complex.conj_mul',
    ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Real.rpow_natCast, ← Real.rpow_add hn]
  congr 2
  ring

end WaveTurbulence.Fourier
