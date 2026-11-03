/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.SymmetricHarmonic
public import Mathlib.Analysis.PSeries
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Paired reciprocal tails

The cancellation in the distant sharp Poisson tail is isolated before
any absolute values are taken. The remainder has a summable square
frequency denominator.
-/

public section

open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- Pairing opposite frequencies removes the nonsummable reciprocal
term, leaving a remainder bounded by `4*r/j²`. -/
theorem norm_paired_reciprocal_sub_le {r j : ℝ} (hr : 0 ≤ r) (hj : 0 < j)
    (hrj : 2 * r ≤ j) (x : ℝ) :
    ‖expPhase (j * x) / ((r + j : ℝ) : ℂ) +
        expPhase (-(j * x)) / ((r - j : ℝ) : ℂ) -
        (expPhase (j * x) - expPhase (-(j * x))) / (j : ℂ)‖ ≤ 4 * r / j ^ 2 := by
  have hplus : 0 < r + j := add_pos_of_nonneg_of_pos hr hj
  have hminus : 0 < j - r := by linarith
  have h1 : |1 / (r + j) - 1 / j| ≤ 2 * r / j ^ 2 := by
    have he : 1 / (r + j) - 1 / j = -r / ((r + j) * j) := by field_simp [hj.ne', hplus.ne', (show r - j ≠ 0 by linarith), hminus.ne']; ring
    rw [he, abs_div, abs_neg, abs_of_nonneg hr, abs_of_pos (mul_pos hplus hj)]
    apply (div_le_div_iff₀ (mul_pos hplus hj) (sq_pos_of_pos hj)).mpr
    nlinarith [mul_nonneg hr hj.le, mul_nonneg hr (sq_nonneg r)]
  have h2 : |1 / (r - j) + 1 / j| ≤ 2 * r / j ^ 2 := by
    have he : 1 / (r - j) + 1 / j = -r / ((j - r) * j) := by field_simp [hj.ne', hplus.ne', (show r - j ≠ 0 by linarith), hminus.ne']; ring
    rw [he, abs_div, abs_neg, abs_of_nonneg hr, abs_of_pos (mul_pos hminus hj)]
    apply (div_le_div_iff₀ (mul_pos hminus hj) (sq_pos_of_pos hj)).mpr
    have hh := mul_nonneg (mul_nonneg hr hj.le) (sub_nonneg.mpr hrj)
    nlinarith
  have heq : expPhase (j * x) / ((r + j : ℝ) : ℂ) +
        expPhase (-(j * x)) / ((r - j : ℝ) : ℂ) -
        (expPhase (j * x) - expPhase (-(j * x))) / (j : ℂ) =
      expPhase (j * x) * ((1 / (r + j) - 1 / j : ℝ) : ℂ) +
      expPhase (-(j * x)) * ((1 / (r - j) + 1 / j : ℝ) : ℂ) := by
    push_cast
    ring
  rw [heq]
  calc
    _ ≤ ‖expPhase (j * x) * ((1 / (r + j) - 1 / j : ℝ) : ℂ)‖ +
        ‖expPhase (-(j * x)) * ((1 / (r - j) + 1 / j : ℝ) : ℂ)‖ := norm_add_le _ _
    _ = |1 / (r + j) - 1 / j| + |1 / (r - j) + 1 / j| := by
      simp only [norm_mul, norm_expPhase, Complex.norm_real, Real.norm_eq_abs, one_mul]
    _ ≤ 2 * r / j ^ 2 + 2 * r / j ^ 2 := add_le_add h1 h2
    _ = 4 * r / j ^ 2 := by ring

/-- For frequencies beyond the derivative range, the paired endpoint
kernel is dominated by a telescoping difference at the range endpoints. -/
theorem abs_paired_reciprocal_le_range {r N j : ℝ} (hr : 0 ≤ r) (hrN : r ≤ N) (hNj : N < j) :
    |1 / (r + j) + 1 / (r - j)| ≤ 1 / (j - N) - 1 / (j + N) := by
  have hj : 0 < j := (hr.trans hrN).trans_lt hNj
  have hjr : 0 < j - r := by linarith
  have hjN : 0 < j - N := sub_pos.mpr hNj
  have hpr : 0 < j + r := add_pos_of_pos_of_nonneg hj hr
  have hpN : 0 < j + N := by linarith
  have heq : 1 / (r + j) + 1 / (r - j) = -(1 / (j - r) - 1 / (j + r)) := by
    rw [show r + j = j + r by ring, show r - j = -(j - r) by ring, div_neg]
    ring
  rw [heq, abs_neg, abs_of_nonneg (sub_nonneg.mpr (one_div_le_one_div_of_le hjr (by linarith)))]
  exact sub_le_sub
    (one_div_le_one_div_of_le hjN (by linarith))
    (one_div_le_one_div_of_le hpr (by linarith))

/-- The cancellation kernel over an arbitrary natural-frequency block. -/
theorem norm_sum_Ioc_pairedHarmonic_le {K L : ℕ} (hKL : K ≤ L) (x : ℝ) :
    ‖∑ j ∈ Finset.Ioc K L,
      (expPhase ((j : ℝ) * x) - expPhase (-((j : ℝ) * x))) / (j : ℂ)‖ ≤ 12 * Real.pi := by
  have hset : Finset.Ioc K L = Finset.Ico (K + 1) (L + 1) := by
    ext j
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hset, Finset.sum_Ico_eq_sub _ (Nat.add_le_add_right hKL 1)]
  exact norm_pairedHarmonic_sub_le L K x

/-- A distant paired block has a uniform bound independent of its upper
cutoff. The second term comes from the summable reciprocal-square error. -/
theorem norm_sum_Ioc_paired_reciprocal_le {r : ℝ} (hr : 0 ≤ r) {K L : ℕ}
    (hK : K ≠ 0) (hKL : K ≤ L) (hrK : 2 * r ≤ K) (x : ℝ) :
    ‖∑ j ∈ Finset.Ioc K L,
      (expPhase ((j : ℝ) * x) / ((r + j : ℝ) : ℂ) +
       expPhase (-((j : ℝ) * x)) / ((r - j : ℝ) : ℂ))‖ ≤
      12 * Real.pi + 4 * r / K := by
  let A : ℕ → ℂ := fun j => expPhase ((j : ℝ) * x) / ((r + j : ℝ) : ℂ) +
    expPhase (-((j : ℝ) * x)) / ((r - j : ℝ) : ℂ)
  let B : ℕ → ℂ := fun j => (expPhase ((j : ℝ) * x) - expPhase (-((j : ℝ) * x))) / (j : ℂ)
  have herr : ‖∑ j ∈ Finset.Ioc K L, (A j - B j)‖ ≤ 4 * r / K := by
    calc
      _ ≤ ∑ j ∈ Finset.Ioc K L, ‖A j - B j‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.Ioc K L, (4 * r * ((j : ℝ) ^ 2)⁻¹) := by
        apply Finset.sum_le_sum
        intro j hj
        obtain ⟨hKj, _⟩ := Finset.mem_Ioc.mp hj
        have hj0 : 0 < (j : ℝ) := by exact_mod_cast (Nat.zero_le K).trans_lt hKj
        have hjr : 2 * r ≤ (j : ℝ) := hrK.trans (by exact_mod_cast hKj.le)
        simpa only [A, B, div_eq_mul_inv, Complex.ofReal_natCast] using norm_paired_reciprocal_sub_le hr hj0 hjr x
      _ = 4 * r * ∑ j ∈ Finset.Ioc K L, ((j : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ 4 * r * ((K : ℝ)⁻¹ - (L : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le_sub hK hKL) (by positivity)
      _ ≤ 4 * r / K := by
        rw [div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg L))
  have heq : (∑ j ∈ Finset.Ioc K L, A j) =
      (∑ j ∈ Finset.Ioc K L, B j) + ∑ j ∈ Finset.Ioc K L, (A j - B j) := by
    rw [Finset.sum_sub_distrib]
    ring
  change ‖∑ j ∈ Finset.Ioc K L, A j‖ ≤ _
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add (norm_sum_Ioc_pairedHarmonic_le hKL x) herr)

end WaveTurbulence.VdCB
