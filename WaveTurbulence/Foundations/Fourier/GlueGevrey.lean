/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.Gevrey
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic

/-!
# Quantitative derivatives of the flat exponential

The building block `expNegInvGlue` has Gevrey-2 bounds. The proof expands
successive derivatives into monomials in `x⁻¹` times the flat exponential,
and bounds the coefficient expansion with factorial weights.
-/

public section

open scoped ContDiff

namespace WaveTurbulence.Fourier

private def nextGlueTerm (p : ℝ × ℕ) : List (ℝ × ℕ) :=
  [(p.1, p.2 + 2), (-p.1 * p.2, p.2 + 1)]

private def glueTerms : ℕ → List (ℝ × ℕ)
  | 0 => [(1, 0)]
  | n + 1 => (glueTerms n).flatMap nextGlueTerm

private noncomputable def glueTerm (p : ℝ × ℕ) (x : ℝ) : ℝ :=
  p.1 * x⁻¹ ^ p.2 * expNegInvGlue x

private noncomputable def glueSum (l : List (ℝ × ℕ)) (x : ℝ) : ℝ :=
  (l.map (fun p => glueTerm p x)).sum

private noncomputable def glueMass (l : List (ℝ × ℕ)) : ℝ :=
  (l.map (fun p => |p.1| * (Nat.factorial p.2 : ℝ))).sum

private theorem hasDerivAt_glueTerm (p : ℝ × ℕ) (x : ℝ) :
    HasDerivAt (glueTerm p) (glueSum (nextGlueTerm p) x) x := by
  rcases p with ⟨a, k⟩
  change HasDerivAt (fun y => a * y⁻¹ ^ k * expNegInvGlue y) _ x
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul
    (Polynomial.C a * Polynomial.X ^ k) x
  simp only [Polynomial.derivative_C_mul_X_pow, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X] at h
  cases k with
  | zero =>
    convert h using 1
    dsimp [glueSum, nextGlueTerm, glueTerm]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  | succ k =>
    convert h using 1
    simp only [glueSum, nextGlueTerm, glueTerm, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero,
        Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    simp only [pow_succ]
    ring

private theorem hasDerivAt_glueSum (l : List (ℝ × ℕ)) (x : ℝ) :
    HasDerivAt (glueSum l) (glueSum (l.flatMap nextGlueTerm) x) x := by
  induction l with
  | nil =>
    change HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 x
    exact hasDerivAt_const x 0
  | cons p l ih =>
    change HasDerivAt (fun y => glueTerm p y + glueSum l y) _ x
    convert (hasDerivAt_glueTerm p x).add ih using 1
    simp [glueSum, List.map_append, List.sum_append]

private theorem iteratedDeriv_glue (n : ℕ) :
    iteratedDeriv n expNegInvGlue = glueSum (glueTerms n) := by
  induction n with
  | zero => funext x; simp [glueTerms, glueSum, glueTerm]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact (hasDerivAt_glueSum (glueTerms n) x).deriv

private theorem glueTerms_degree (n : ℕ) :
    ∀ p ∈ glueTerms n, p.2 ≤ 2 * n := by
  induction n with
  | zero => simp [glueTerms]
  | succ n ih =>
    intro p hp
    obtain ⟨q, hq, hp⟩ := List.mem_flatMap.mp hp
    have h := ih q hq
    simp only [nextGlueTerm, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp <;> omega

private theorem glueMass_next (p : ℝ × ℕ) :
    glueMass (nextGlueTerm p) =
      |p.1| * ((p.2 + 2 : ℝ) * (p.2 + 1) + p.2 * (p.2 + 1)) *
        (Nat.factorial p.2 : ℝ) := by
  simp [glueMass, nextGlueTerm, Nat.factorial_succ, abs_mul, Nat.abs_cast,
    Nat.cast_add, Nat.cast_mul]
  ring

private theorem glueMass_flatMap (l : List (ℝ × ℕ)) :
    glueMass (l.flatMap nextGlueTerm) = (l.map fun p => glueMass (nextGlueTerm p)).sum := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    change glueMass (nextGlueTerm p ++ l.flatMap nextGlueTerm) = _
    simp only [glueMass, List.map_append, List.sum_append, List.map_cons, List.sum_cons] at *
    rw [ih]

private theorem glueMass_bound (n : ℕ) :
    glueMass (glueTerms n) ≤ (2 : ℝ) ^ n * Nat.factorial (2 * n) := by
  induction n with
  | zero => simp [glueMass, glueTerms]
  | succ n ih =>
    have ht (p : ℝ × ℕ) (hp : p ∈ glueTerms n) :
        glueMass (nextGlueTerm p) ≤
          (2 * (2 * n + 2 : ℝ) * (2 * n + 1)) *
            (|p.1| * (Nat.factorial p.2 : ℝ)) := by
      rw [glueMass_next]
      have hk : (p.2 : ℝ) ≤ 2 * n := by exact_mod_cast glueTerms_degree n p hp
      have hk0 : (0 : ℝ) ≤ p.2 := Nat.cast_nonneg _
      have he : (p.2 + 2 : ℝ) * (p.2 + 1) + p.2 * (p.2 + 1) ≤
          2 * (2 * n + 2) * (2 * n + 1) := by nlinarith
      calc
        _ = (|p.1| * (Nat.factorial p.2 : ℝ)) *
            ((p.2 + 2 : ℝ) * (p.2 + 1) + p.2 * (p.2 + 1)) := by ring
        _ ≤ _ := by
          simpa only [mul_comm] using mul_le_mul_of_nonneg_left he
            (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
    calc
      glueMass (glueTerms (n + 1)) =
          ((glueTerms n).map fun p => glueMass (nextGlueTerm p)).sum :=
        glueMass_flatMap _
      _ ≤ ((glueTerms n).map fun p =>
          (2 * (2 * n + 2 : ℝ) * (2 * n + 1)) *
            (|p.1| * (Nat.factorial p.2 : ℝ))).sum :=
        by
          have hs (l : List (ℝ × ℕ))
              (hl : ∀ p ∈ l, glueMass (nextGlueTerm p) ≤
                (2 * (2 * n + 2 : ℝ) * (2 * n + 1)) *
                  (|p.1| * (Nat.factorial p.2 : ℝ))) :
              (l.map fun p => glueMass (nextGlueTerm p)).sum ≤
                (l.map fun p => (2 * (2 * n + 2 : ℝ) * (2 * n + 1)) *
                  (|p.1| * (Nat.factorial p.2 : ℝ))).sum := by
            induction l with
            | nil => simp
            | cons p l ih =>
              simp only [List.map_cons, List.sum_cons]
              exact add_le_add (hl p (by simp)) (ih (fun q hq => hl q (by simp [hq])))
          exact hs _ ht
      _ = (2 * (2 * n + 2 : ℝ) * (2 * n + 1)) * glueMass (glueTerms n) := by
        simp [glueMass, ← List.sum_map_mul_left]
      _ ≤ (2 * (2 * n + 2 : ℝ) * (2 * n + 1)) *
          ((2 : ℝ) ^ n * Nat.factorial (2 * n)) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ = (2 : ℝ) ^ (n + 1) * Nat.factorial (2 * (n + 1)) := by
        rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
          Nat.factorial_succ, Nat.factorial_succ, pow_succ]
        push_cast
        ring

private theorem glue_monomial_bound (k : ℕ) (x : ℝ) :
    |x⁻¹ ^ k * expNegInvGlue x| ≤ (Nat.factorial k : ℝ) := by
  by_cases hx : x ≤ 0
  · simp [expNegInvGlue.zero_of_nonpos hx]
  have hx0 : 0 ≤ x⁻¹ := inv_nonneg.mpr (le_of_not_ge hx)
  have he := Real.pow_div_factorial_le_exp x⁻¹ hx0 k
  have hf : (0 : ℝ) < Nat.factorial k := Nat.cast_pos.mpr (Nat.factorial_pos _)
  rw [div_le_iff₀ hf] at he
  simp only [expNegInvGlue, ite_eq_right (by exact hx), abs_of_nonneg
    (mul_nonneg (pow_nonneg hx0 _) (Real.exp_pos _).le)]
  calc
    x⁻¹ ^ k * Real.exp (-x⁻¹) ≤
        (Real.exp x⁻¹ * Nat.factorial k) * Real.exp (-x⁻¹) :=
      mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ = Nat.factorial k := by rw [mul_right_comm, ← Real.exp_add]; simp

private theorem glueSum_bound (l : List (ℝ × ℕ)) (x : ℝ) :
    |glueSum l x| ≤ glueMass l := by
  induction l with
  | nil => simp [glueSum, glueMass]
  | cons p l ih =>
    have ht : |glueTerm p x| ≤ |p.1| * (Nat.factorial p.2 : ℝ) := by
      simpa only [glueTerm, mul_assoc, abs_mul] using
        mul_le_mul_of_nonneg_left (glue_monomial_bound p.2 x) (abs_nonneg p.1)
    simpa only [glueSum, glueMass, List.map_cons, List.sum_cons] using
      (abs_add_le (glueTerm p x) (glueSum l x)).trans (add_le_add ht ih)

/-- The flat exponential has the explicit absolute Gevrey constants `C=1`,
`A=2` in the normalization of erratum F41. -/
theorem expNegInvGlue_gevreyTwoBound : GevreyTwoBound expNegInvGlue 1 2 := by
  intro n x
  rw [iteratedDeriv_glue]
  simpa only [one_mul] using (glueSum_bound (glueTerms n) x).trans (glueMass_bound n)

end WaveTurbulence.Fourier
