/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LemLin.ScalarPoisson
public import WaveTurbulence.Foundations.LemLin.LinearSum

/-!
# Finite scalar cutoff sums

Compact support gives a fixed finite index interval for every frequency.
This supplies continuity, the elementary `3L` bound, and conjugation symmetry.
-/

public section

namespace WaveTurbulence.LemLin
open Finset MeasureTheory
open scoped Classical

/-- The exact integer interval containing the support of a scalar cutoff. -/
@[expose] noncomputable def scalarIndexSet (L a : ℝ) : Finset ℤ :=
  Counting.integerInterval (L * a - L) (L * a + L)

theorem chi0Complex_nonzero_mem_scalarIndexSet {L : ℝ} (hL : 0 < L) (a : ℝ) (n : ℤ)
    (hn : Fourier.chi0Complex ((n : ℝ) / L - a) ≠ 0) : n ∈ scalarIndexSet L a := by
  have hi : |(n : ℝ) / L - a| < 1 := by
    by_contra h
    apply hn
    simp only [Fourier.chi0Complex, Fourier.chi0_eq_zero (le_of_not_gt h), Complex.ofReal_zero]
  apply (Counting.mem_integerInterval n (L * a - L) (L * a + L)).mpr
  have heq : (n : ℝ) - L * a = L * ((n : ℝ) / L - a) := by field_simp
  have hb : |(n : ℝ) - L * a| ≤ L := by
    rw [heq, abs_mul, abs_of_pos hL]
    nlinarith only [hi, hL]
  obtain ⟨hlo, hhi⟩ := abs_le.mp hb
  constructor <;> linarith

/-- The scalar lattice sum is finite on an interval independent of frequency. -/
theorem scalarLatticeSum_eq_sum {L : ℝ} (hL : 0 < L) (a u : ℝ) :
    scalarLatticeSum L a u = ∑ n ∈ scalarIndexSet L a,
      scalarAmplitude a u ((n : ℝ) / L) := by
  apply tsum_eq_sum
  intro n hn
  have hz : Fourier.chi0Complex ((n : ℝ) / L - a) = 0 := by
    by_contra hz
    exact hn (chi0Complex_nonzero_mem_scalarIndexSet hL a n hz)
  simp only [scalarAmplitude, hz, zero_mul]

/-- Scalar elementary bound in TARGET `lemlin`. -/
theorem norm_scalarLatticeSum_le {L : ℝ} (hL : 1 ≤ L) (a u : ℝ) :
    ‖scalarLatticeSum L a u‖ ≤ 3 * L := by
  have hLpos : 0 < L := by linarith
  rw [scalarLatticeSum_eq_sum hLpos]
  calc
    _ ≤ ∑ _n ∈ scalarIndexSet L a, (1 : ℝ) := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro n _
      simp only [scalarAmplitude, norm_mul, Circle.norm_coe, mul_one,
        Fourier.chi0Complex, Complex.norm_real, Real.norm_of_nonneg (Fourier.chi0_nonneg _)]
      exact Fourier.chi0_le_one _
    _ = ((scalarIndexSet L a).card : ℝ) := by simp
    _ ≤ 2 * L + 1 := Counting.card_integerInterval_le (L * a) hLpos.le
    _ ≤ _ := by linarith

/-- Continuity of the scalar cutoff sum in frequency. -/
theorem continuous_scalarLatticeSum {L : ℝ} (hL : 0 < L) (a : ℝ) :
    Continuous (scalarLatticeSum L a) := by
  have heq : scalarLatticeSum L a = fun u => ∑ n ∈ scalarIndexSet L a,
      scalarAmplitude a u ((n : ℝ) / L) := funext (scalarLatticeSum_eq_sum hL a)
  rw [heq]
  unfold scalarAmplitude
  fun_prop

/-- A real cutoff has an even absolute Fourier sum. -/
theorem norm_scalarLatticeSum_neg {L : ℝ} (hL : 0 < L) (a u : ℝ) :
    ‖scalarLatticeSum L a (-u)‖ = ‖scalarLatticeSum L a u‖ := by
  have heq : scalarLatticeSum L a (-u) = star (scalarLatticeSum L a u) := by
    simp only [scalarLatticeSum_eq_sum hL, star_sum]
    apply sum_congr rfl
    intro n _
    simp only [scalarAmplitude, Fourier.chi0Complex, Complex.star_def, map_mul,
      Complex.conj_ofReal, Real.fourierChar_apply, ← Complex.exp_conj, Complex.conj_I]
    congr 1
    push_cast
    ring_nf

  rw [heq, norm_star]

end WaveTurbulence.LemLin
