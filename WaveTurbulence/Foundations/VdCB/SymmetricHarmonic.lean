/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
The symmetric-interval splitting adapts the landed NumberTheory/SawtoothFourier.lean
(derived from Jason Hickey's Salt/Weil/Sawtooth.lean; see docs/THIRD-PARTY.md).
-/
module

public import WaveTurbulence.Foundations.VdCB.PairedHarmonic

/-!
# The paired harmonic kernel

This is the cancellation kernel in the distant part of the sharp Poisson
frequency tail. Its norm is uniformly bounded, whereas the absolute sum
of the separate positive and negative frequencies is divergent.
-/

public section

open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- Pair positive and negative harmonic frequencies before summing.
The zero term of the finite range is identically zero. -/
@[expose] noncomputable def pairedHarmonic (K : ℕ) (x : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (K + 1), (expPhase ((j : ℝ) * x) - expPhase (-((j : ℝ) * x))) / (j : ℂ)

private theorem symmetric_erase_succ (K : ℕ) :
    (Finset.Icc (-((K : ℤ) + 1)) ((K : ℤ) + 1)).erase 0 =
      insert ((K : ℤ) + 1) (insert (-((K : ℤ) + 1)) ((Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0)) := by
  ext j
  simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_insert]
  omega

/-- The paired kernel is exactly the symmetric sawtooth Fourier truncation. -/
theorem pairedHarmonic_eq (K : ℕ) (x : ℝ) :
    pairedHarmonic K x = -(2 * (Real.pi : ℂ) * Complex.I) * sawtoothFourier K x := by
  unfold pairedHarmonic sawtoothFourier
  induction K with
  | zero => simp
  | succ K ih =>
      have hn1 : ((K : ℤ) + 1) ∉ insert (-((K : ℤ) + 1)) ((Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0) := by
        simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_Icc]
        omega
      have hn2 : (-((K : ℤ) + 1)) ∉ (Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0 := by
        simp only [Finset.mem_erase, Finset.mem_Icc]
        omega
      have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
      have hj : (K : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero K)
      rw [Nat.cast_add, Nat.cast_one, symmetric_erase_succ, Finset.sum_insert hn1,
        Finset.sum_insert hn2, Finset.sum_range_succ]
      rw [ih]
      push_cast
      simp only [neg_mul]
      field_simp
      simp only [mul_comm]
      ring

/-- Uniform boundedness of a block of the paired harmonic kernel. -/
theorem norm_pairedHarmonic_sub_le (K L : ℕ) (x : ℝ) :
    ‖pairedHarmonic K x - pairedHarmonic L x‖ ≤ 12 * Real.pi := by
  rw [pairedHarmonic_eq, pairedHarmonic_eq, ← mul_sub, norm_mul, norm_neg]
  have hc : ‖2 * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
    norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hc]
  have hh := mul_le_mul_of_nonneg_left (norm_sawtoothFourier_sub_le_six K L x) (by positivity : 0 ≤ 2 * Real.pi)
  convert hh using 1
  ring

end WaveTurbulence.VdCB
