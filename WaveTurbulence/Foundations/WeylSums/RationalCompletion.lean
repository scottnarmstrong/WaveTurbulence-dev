/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.CompleteGauss
public import WaveTurbulence.Foundations.WeylSums.Geometric

/-!
# Rational completion of real quadratic phases

The periodic rational part is expanded exactly in finitely many linear
frequencies. Each coefficient is `O(q⁻¹ᐟ²)`, uniformly in its frequency.
-/

public section

open scoped BigOperators
open Finset

namespace WaveTurbulence.WeylSums

/-- The standard finite additive character agrees with `exp(2πit)`. -/
theorem stdAddChar_int_eq_e (m : ℤ) (q : ℕ) [NeZero q] :
    ZMod.stdAddChar (m : ZMod q) = e ((m : ℝ) / q) := by
  rw [ZMod.stdAddChar_coe]
  unfold e
  congr 1
  push_cast
  ring

/-- Coprime integer numerators represent units modulo the denominator. -/
theorem isUnit_intCast_of_coprime (a : ℤ) (q : ℕ) (ha : a.natAbs.Coprime q) :
    IsUnit (a : ZMod q) := by
  have hu := (ZMod.isUnit_iff_coprime a.natAbs q).mpr ha
  have hu' : IsUnit ((|a| : ℤ) : ZMod q) := by
    rw [← Int.cast_natCast, Int.natCast_natAbs] at hu
    exact hu
  rcases abs_cases a with ⟨heq, _⟩ | ⟨heq, _⟩
  · rwa [heq] at hu'
  · rw [heq, Int.cast_neg] at hu'
    simpa only [neg_neg] using hu'.neg

/-- Exact completion of the rational quadratic part of a real phase. -/
theorem rational_phase_completion (a x : ℤ) (q : ℕ) [NeZero q] :
    e ((a : ℝ) / q * (x : ℝ) ^ 2) =
      ∑ b : ZMod q, quadraticFourierCoeff (a : ZMod q) b * e ((b.val : ℝ) / q * x) := by
  have h := quadratic_completion (a : ZMod q) (x : ZMod q)
  have hleft : ZMod.stdAddChar ((a : ZMod q) * (x : ZMod q) ^ 2) =
      e ((a : ℝ) / q * (x : ℝ) ^ 2) := by
    rw [← Int.cast_pow, ← Int.cast_mul, stdAddChar_int_eq_e]
    congr 1
    push_cast
    ring
  have hright (b : ZMod q) : ZMod.stdAddChar (b * (x : ZMod q)) =
      e ((b.val : ℝ) / q * x) := by
    nth_rw 1 [← ZMod.natCast_zmod_val b]
    rw [← Int.cast_natCast, ← Int.cast_mul, stdAddChar_int_eq_e]
    congr 1
    push_cast
    ring
  simpa only [hleft, hright] using h

/-- Finite weighted rational completion. The weight may be complex and is
unrestricted; no estimate on it is assumed here. -/
theorem weighted_rational_completion (S : Finset ℤ) (w : ℤ → ℂ)
    (a : ℤ) (q : ℕ) [NeZero q] (β r : ℝ) :
    (∑ x ∈ S, w x * e (((a : ℝ) / q + β) * (x : ℝ) ^ 2 + r * x)) =
      ∑ b : ZMod q, quadraticFourierCoeff (a : ZMod q) b *
        ∑ x ∈ S, w x * e (β * (x : ℝ) ^ 2 + (r + (b.val : ℝ) / q) * x) := by
  have hphase (x : ℤ) : ((a : ℝ) / q + β) * (x : ℝ) ^ 2 + r * x =
      (a : ℝ) / q * (x : ℝ) ^ 2 + (β * (x : ℝ) ^ 2 + r * x) := by ring
  simp_rw [hphase, e_add, rational_phase_completion]
  simp only [mul_assoc, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro x _
  simp only [← e_add]
  rw [show (b.val : ℝ) / q * (x : ℝ) + (β * (x : ℝ) ^ 2 + r * x) =
    β * (x : ℝ) ^ 2 + (r + (b.val : ℝ) / q) * x by ring]
  ring

end WaveTurbulence.WeylSums
