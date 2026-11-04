/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.SymmetricHarmonic
public import WaveTurbulence.Foundations.VdCB.Phase
public import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# The symmetric Dirichlet kernel and the sawtooth primitive

The finite sawtooth Fourier sum has derivative `1-D_K` and vanishes
at integer arguments. These exact identities retain the midpoint
endpoint convention in sharp Poisson summation.
-/

public section

open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- The symmetric Dirichlet kernel in the normalized character convention. -/
@[expose] noncomputable def symmetricKernel (K : ℕ) (x : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), expPhase ((m : ℝ) * x)

theorem expPhase_intCast (n : ℤ) : expPhase (n : ℝ) = 1 := by
  simpa only [zero_add, expPhase_zero] using expPhase_add_intCast 0 n

/-- The finite harmonic cancellation gives zero at every integer endpoint. -/
theorem sawtoothFourier_intCast (K : ℕ) (n : ℤ) : sawtoothFourier K (n : ℝ) = 0 := by
  have hp : pairedHarmonic K (n : ℝ) = 0 := by
    unfold pairedHarmonic
    apply Finset.sum_eq_zero
    intro j hj
    have h1 : expPhase ((j : ℝ) * (n : ℝ)) = 1 := by
      simpa only [Int.cast_mul, Int.cast_natCast] using expPhase_intCast ((j : ℤ) * n)
    have h2 : expPhase (-((j : ℝ) * (n : ℝ))) = 1 := by
      rw [expPhase_neg, h1, inv_one]
    rw [h1, h2, sub_self, zero_div]
  have hh := pairedHarmonic_eq K (n : ℝ)
  rw [hp] at hh
  have hc : -(2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
  exact (mul_eq_zero.mp hh.symm).resolve_left hc

/-- The actual derivative of the finite sawtooth primitive. -/
theorem hasDerivAt_sawtoothFourier (K : ℕ) (x : ℝ) :
    HasDerivAt (sawtoothFourier K) (1 - symmetricKernel K x) x := by
  let S := (Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have ht (m : ℤ) (hm : m ∈ S) :
      HasDerivAt (fun y => expPhase ((m : ℝ) * y) / (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)))
        (expPhase ((m : ℝ) * x)) x := by
    have hm0 : m ≠ 0 := (Finset.mem_erase.mp hm).1
    have hmC : (m : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hm0
    have hd := (hasDerivAt_expPhase_comp ((hasDerivAt_id x).const_mul (m : ℝ))).div_const
      (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ))
    convert hd using 1
    · funext y
      rfl
    · simp only [mul_one, id_eq]
      push_cast
      field_simp
  have hsum := (HasDerivAt.fun_sum (u := S) (fun m hm => ht m hm)).neg
  have h0 : (0 : ℤ) ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by simp only [Finset.mem_Icc]; omega
  have hsplit := Finset.sum_erase_add (Finset.Icc (-(K : ℤ)) (K : ℤ))
    (fun m : ℤ => expPhase ((m : ℝ) * x)) h0
  simp only [Int.cast_zero, zero_mul, expPhase_zero] at hsplit
  convert hsum using 1
  · funext y
    rfl
  · unfold symmetricKernel
    rw [← hsplit]
    dsimp only [S]
    ring

end WaveTurbulence.VdCB
