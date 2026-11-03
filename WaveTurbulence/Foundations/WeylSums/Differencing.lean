/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Weyl differencing identities

Squaring a quadratic exponential sum produces linear exponential sums, the
first step of the route to the Gauss lemma used in DH23 Lemma 6.6.
-/

public section

open scoped BigOperators ComplexConjugate
open Finset

namespace WaveTurbulence.WeylSums

/-- Reindex the strictly lower triangular part of a square by positive differences. -/
theorem sum_triangle_eq_sum_differences {M : Type*} [AddCommMonoid M]
    (f : ℕ → ℕ → M) (N : ℕ) :
    (∑ i ∈ range N, ∑ j ∈ range i, f i j) =
      ∑ d ∈ range N, ∑ j ∈ range (N - (d + 1)), f (j + d + 1) j := by
  rw [sum_sigma', sum_sigma']
  refine sum_bij (fun a _ => ⟨a.1 - a.2 - 1, a.2⟩) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [mem_sigma, mem_range] at ha ⊢
    omega
  · intro a ha b hb hab
    simp only [mem_sigma, mem_range] at ha hb
    have h₁ := congrArg Sigma.fst hab
    have h₂ := congrArg Sigma.snd hab
    apply Sigma.ext
    · dsimp at h₁ h₂
      omega
    · simpa using h₂
  · intro b hb
    simp only [mem_sigma, mem_range] at hb
    refine ⟨⟨b.2 + b.1 + 1, b.2⟩, ?_, ?_⟩
    · simp only [mem_sigma, mem_range]
      omega
    · apply Sigma.ext
      · dsimp
        omega
      · rfl
  · intro a ha
    simp only [mem_sigma, mem_range] at ha
    congr 1
    dsimp
    omega

/-- Exact square expansion of an arbitrary complex sum, before differencing. -/
theorem norm_sum_sq_eq_triangle (z : ℕ → ℂ) (N : ℕ) :
    ‖∑ j ∈ range N, z j‖ ^ 2 =
      (∑ j ∈ range N, ‖z j‖ ^ 2) +
      2 * ∑ i ∈ range N, (∑ j ∈ range i, z i * conj (z j)).re := by
  simp_rw [← Complex.normSq_eq_norm_sq]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, Complex.normSq_add, ih, sum_range_succ, sum_range_succ]
    have hcross : ((∑ j ∈ range N, z j) * conj (z N)).re =
        (∑ j ∈ range N, z N * conj (z j)).re := by
      rw [sum_mul, Complex.re_sum, Complex.re_sum]
      apply sum_congr rfl
      intro j _
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    rw [hcross]
    ring

/-- Exact square expansion indexed by the positive differences. -/
theorem norm_sum_sq_eq_differences (z : ℕ → ℂ) (N : ℕ) :
    ‖∑ j ∈ range N, z j‖ ^ 2 =
      (∑ j ∈ range N, ‖z j‖ ^ 2) +
      2 * ∑ d ∈ range N, (∑ j ∈ range (N - (d + 1)),
        z (j + d + 1) * conj (z j)).re := by
  rw [norm_sum_sq_eq_triangle]
  simp_rw [Complex.re_sum]
  rw [sum_triangle_eq_sum_differences]

/-- A quadratic phase difference is a linear phase times a constant of modulus one. -/
theorem quadratic_phase_difference (s r x d : ℝ) :
    e (s * (x + d) ^ 2 + r * (x + d)) * conj (e (s * x ^ 2 + r * x)) =
      e (s * d ^ 2 + r * d) * e ((2 * s * d) * x) := by
  rw [← Complex.inv_eq_conj (norm_e _), ← div_eq_mul_inv, ← e_sub, ← e_add]
  congr 1
  ring

/-- The correlation sums in quadratic Weyl differencing are linear sums in norm. -/
theorem norm_quadratic_correlation (s r : ℝ) (d N : ℕ) :
    ‖∑ j ∈ range N, e (s * ((j : ℝ) + d) ^ 2 + r * ((j : ℝ) + d)) *
      conj (e (s * (j : ℝ) ^ 2 + r * j))‖ = ‖linearSum (2 * s * d) N‖ := by
  simp_rw [quadratic_phase_difference]
  rw [← mul_sum, norm_mul, norm_e, one_mul]
  rfl

/-- Weyl differencing with all constants explicit and uniform in the shift and
linear frequency. This is the squaring step toward DH23's Gauss lemma, not the
rational-approximation estimate itself. -/
theorem norm_gaussSum_sq_le_differencing (s r : ℝ) (h : ℤ) (n : ℕ) :
    ‖gaussSum s r h n‖ ^ 2 ≤ (n : ℝ) + 1 +
      2 * ∑ d ∈ range (n + 1), ‖linearSum (2 * s * (d + 1)) (n - d)‖ := by
  rw [norm_gaussSum_shift]
  let r' := r + 2 * s * h
  have hexpand := norm_sum_sq_eq_differences (fun j => e (s * (j : ℝ) ^ 2 + r' * j))
    (n + 1)
  simp only [norm_e, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one,
    Nat.cast_add, Nat.cast_one] at hexpand
  have hsum : gaussSum s r' 0 n = ∑ j ∈ range (n + 1), e (s * (j : ℝ) ^ 2 + r' * j) := by
    simp only [gaussSum, Int.cast_zero, zero_add]
  rw [show gaussSum s (r + 2 * s * ↑h) 0 n = gaussSum s r' 0 n from rfl, hsum, hexpand]
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply sum_le_sum
  intro d _
  refine (Complex.re_le_norm _).trans ?_
  have hlen : n + 1 - (d + 1) = n - d := by omega
  rw [hlen]
  exact (by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
      (norm_quadratic_correlation s r' (d + 1) (n - d)).le)


end WaveTurbulence.WeylSums
