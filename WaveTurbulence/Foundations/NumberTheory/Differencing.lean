/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Positivity

/-!
# Finite Weyl differencing

The averaging and Cauchy–Schwarz step in the A-process, NT-CIRCLE-v2 goal 1.
The final inequality applies to any finite additive group and any finite set
of shifts. Integer interval sums can be embedded in a sufficiently large cyclic
group without wrapping their support. No derivative estimate is assumed here.
-/

public section

open scoped BigOperators ComplexConjugate

namespace WaveTurbulence.NumberTheory

/-- Cauchy–Schwarz for a finite complex sum, with the cardinal factor explicit. -/
theorem norm_sum_sq_le_card_mul_sum_norm_sq {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  calc
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s f) 2
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := sq_sum_le_card_mul_sum_sq

/-- The squared norm of a sum is the real part of its pair correlations. -/
theorem norm_sum_sq_eq_sum_re {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ∑ j ∈ s, (f i * conj (f j)).re := by
  rw [← Complex.ofReal_re (‖∑ i ∈ s, f i‖ ^ 2), Complex.ofReal_pow,
    ← Complex.mul_conj']
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [Complex.re_sum]

/-- Averaging translates of a finite sum multiplies it by the number of shifts. -/
theorem sum_sum_add_eq_card_mul {G : Type*} [AddGroup G] [Fintype G]
    (s : Finset G) (f : G → ℂ) :
    (∑ x : G, ∑ h ∈ s, f (x + h)) = (s.card : ℂ) * ∑ x : G, f x := by
  classical
  rw [Finset.sum_comm]
  have htranslate (h : G) : (∑ x : G, f (x + h)) = ∑ x : G, f x :=
    Equiv.sum_comp (Equiv.addRight h) f
  simp only [htranslate, Finset.sum_const, nsmul_eq_mul]

/-- Weyl differencing on a finite additive group. Both the averaging scale and
the ambient cardinal factor are explicit; the right side consists of norms of
correlation sums, rather than sums of the individual term norms. -/
theorem weyl_differencing_finite {G : Type*} [AddGroup G] [Fintype G]
    (s : Finset G) (f : G → ℂ) :
    (s.card : ℝ) ^ 2 * ‖∑ x : G, f x‖ ^ 2 ≤
      (Fintype.card G : ℝ) * ∑ h ∈ s, ∑ k ∈ s,
        ‖∑ x : G, f (x + h) * conj (f (x + k))‖ := by
  classical
  have hcs := norm_sum_sq_le_card_mul_sum_norm_sq Finset.univ
    (fun x : G => ∑ h ∈ s, f (x + h))
  rw [sum_sum_add_eq_card_mul, norm_mul, Complex.norm_natCast, mul_pow,
    Finset.card_univ] at hcs
  refine hcs.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  simp_rw [norm_sum_sq_eq_sum_re]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro h _
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro k _
  rw [← Complex.re_sum]
  exact Complex.re_le_norm _

end WaveTurbulence.NumberTheory
