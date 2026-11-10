/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cumulant.Inversion
public import WaveTurbulence.Foundations.Combinatorics.PartitionCount
public import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Factorial moment–cumulant bounds

TARGET L813–L815 uses the finite partition identities to exchange moments and
cumulants with `(C₀ R)!` losses. Here blockwise bounds with constant `C₀` yield
whole-set bounds with constant `C₀+2`. The underlying measure can be restricted
and need not be normalized. These are conditional bounds, not assertions of
moment estimates for a particular random field.
-/

public section

namespace WaveTurbulence.Probability
open MeasureTheory Finset
open scoped Classical

variable {ι : Type*} [DecidableEq ι] {s : Finset ι}

/-- Products of the factorial block losses are bounded by the total factorial. -/
lemma prod_factorial_parts_le (P : Finpartition s) (C₀ : ℕ) :
    ∏ A ∈ P.parts, (C₀ * A.card).factorial ≤ (C₀ * s.card).factorial := by
  have h := Nat.le_of_dvd (Nat.factorial_pos (∑ A ∈ P.parts, C₀ * A.card))
    (Nat.prod_factorial_dvd_factorial_sum P.parts (fun A => C₀ * A.card))
  simpa only [← mul_sum, P.sum_card_parts] using h

/-- The partition-count and coefficient losses can be absorbed into two extra factorial units. -/
lemma partition_factorial_loss (C₀ : ℕ) :
    Fintype.card (Finpartition s) * s.card.factorial * (C₀ * s.card).factorial ≤
      ((C₀ + 2) * s.card).factorial := by
  calc
    _ ≤ (2 * s.card).factorial * (C₀ * s.card).factorial :=
      Nat.mul_le_mul_right _ Combinatorics.card_finpartition_mul_factorial_le
    _ ≤ (2 * s.card + C₀ * s.card).factorial :=
      Nat.le_of_dvd (Nat.factorial_pos _)
        (Nat.factorial_mul_factorial_dvd_factorial_add _ _)
    _ = _ := by congr 1; ring

end WaveTurbulence.Probability
