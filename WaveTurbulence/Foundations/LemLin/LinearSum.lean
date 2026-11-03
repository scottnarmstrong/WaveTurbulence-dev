/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Frozen.Defs.LatticePoint
public import WaveTurbulence.Foundations.Fourier.CutoffPhase
public import WaveTurbulence.Foundations.Counting.LatticeBox

/-!
# The cutoff linear lattice sum

TARGET Lemma `lemlin`, L1536–L1543. The sum is over the actual scaled lattice,
with the frozen Euclidean momentum carrier and the paper's fixed tensor cutoff.
Compact support turns the sum into a finite sum on an explicitly bounded box.
-/

public section

namespace WaveTurbulence.LemLin
open MeasureTheory Finset WithLp
open scoped Classical InnerProductSpace

/-- The exponential sum in TARGET `lemlin`, with frequency `w`. -/
@[expose] noncomputable def linearLatticeSum {d : ℕ} (L : ℝ) (a w : Mom d) : ℂ :=
  ∑' n : Fin d → ℤ, Fourier.chi0TensorComplex (ofLp (latticePoint L n - a)) *
    (Real.fourierChar ⟪w, latticePoint L n⟫_ℝ : ℂ)

/-- The finite index box for a translated cutoff. -/
@[expose] noncomputable def cutoffIndexBox {d : ℕ} (L : ℝ) (a : Mom d) :
    Finset (Fin d → ℤ) := Counting.latticeBox (fun i => L * a i) L

/-- A nonzero cutoff summand lies in the explicit index box. -/
theorem cutoff_nonzero_mem_box {d : ℕ} {L : ℝ} (hL : 0 < L) (a : Mom d)
    (n : Fin d → ℤ) (hn : Fourier.chi0TensorComplex (ofLp (latticePoint L n - a)) ≠ 0) :
    n ∈ cutoffIndexBox L a := by
  apply (Counting.mem_latticeBox _ _ _).mpr
  intro i
  have hi : |(n i : ℝ) / L - a i| < 1 := by
    by_contra h
    apply hn
    unfold Fourier.chi0TensorComplex
    rw [Fourier.chi0Tensor_eq_zero i (by
      change 1 ≤ |(n i : ℝ) / L - a i|
      exact le_of_not_gt h), Complex.ofReal_zero]
  have heq : (n i : ℝ) - L * a i = L * ((n i : ℝ) / L - a i) := by field_simp
  rw [heq, abs_mul, abs_of_pos hL]
  nlinarith only [hi, hL]

/-- TARGET `lemlin`: the infinite sum equals a finite sum, uniformly in frequency. -/
theorem linearLatticeSum_eq_sum {d : ℕ} {L : ℝ} (hL : 0 < L) (a w : Mom d) :
    linearLatticeSum L a w = ∑ n ∈ cutoffIndexBox L a,
      Fourier.chi0TensorComplex (ofLp (latticePoint L n - a)) *
        (Real.fourierChar ⟪w, latticePoint L n⟫_ℝ : ℂ) := by
  apply tsum_eq_sum
  intro n hn
  have hz : Fourier.chi0TensorComplex (ofLp (latticePoint L n - a)) = 0 := by
    by_contra hz
    exact hn (cutoff_nonzero_mem_box hL a n hz)
  rw [hz, zero_mul]

/-- The elementary pointwise bound in TARGET `lemlin`. -/
theorem norm_linearLatticeSum_le {d : ℕ} {L : ℝ} (hL : 1 ≤ L) (a w : Mom d) :
    ‖linearLatticeSum L a w‖ ≤ (3 : ℝ) ^ d * L ^ d := by
  have hLpos : 0 < L := by linarith
  rw [linearLatticeSum_eq_sum hLpos]
  calc
    _ ≤ ∑ _n ∈ cutoffIndexBox L a, (1 : ℝ) := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro n _
      rw [norm_mul, Circle.norm_coe, mul_one]
      simpa only [Fourier.chi0TensorComplex, Complex.norm_real,
        Real.norm_of_nonneg (Fourier.chi0Tensor_nonneg _)] using
          Fourier.chi0Tensor_le_one (ofLp (latticePoint L n - a))
    _ = ((cutoffIndexBox L a).card : ℝ) := by simp
    _ ≤ (2 * L + 1) ^ d := Counting.card_latticeBox_le _ hLpos.le
    _ ≤ (3 * L) ^ d := pow_le_pow_left₀ (by positivity) (by linarith) d
    _ = _ := mul_pow _ _ _

/-- The linear lattice sum is continuous as a function of its frequency. -/
theorem continuous_linearLatticeSum {d : ℕ} {L : ℝ} (hL : 0 < L) (a : Mom d) :
    Continuous (linearLatticeSum L a) := by
  have heq : linearLatticeSum L a = fun w => ∑ n ∈ cutoffIndexBox L a,
      Fourier.chi0TensorComplex (ofLp (latticePoint L n - a)) *
        (Real.fourierChar ⟪w, latticePoint L n⟫_ℝ : ℂ) :=
    funext (linearLatticeSum_eq_sum hL a)
  rw [heq]
  fun_prop

end WaveTurbulence.LemLin
