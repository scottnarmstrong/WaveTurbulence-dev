/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.GronwallUniform

/-!
# Recursive constants for weighted jet persistence

These are the constants C(s,m,T,A,B) in TARGET (schappend10). The precise
lower-order combinatorial factor follows the ordered-word convention.
-/

public section

noncomputable section

namespace WaveTurbulence.WKEL2

/-- Uniform jet bound, recursively using only the preceding order in the forcing term. -/
@[expose] def jetGronwallBound (C T A B : ℝ) : ℕ → ℝ
  | 0 => A
  | n + 1 => max (jetGronwallBound C T A B n)
      (gronwallBound B (12 * C * A ^ 2)
        (4 * 3 ^ (n + 1) * C * jetGronwallBound C T A B n ^ 3) T)

theorem jetGronwallBound_zero (C T A B : ℝ) : jetGronwallBound C T A B 0 = A := rfl

/-- The recursive constants remain nonnegative. -/
theorem jetGronwallBound_nonneg (C T A B : ℝ) (hA : 0 ≤ A) :
    ∀ n, 0 ≤ jetGronwallBound C T A B n
  | 0 => hA
  | n + 1 => (jetGronwallBound_nonneg C T A B hA n).trans (le_max_left _ _)

/-- Each new constant includes every already-controlled lower order. -/
theorem jetGronwallBound_le_succ (C T A B : ℝ) (n : ℕ) :
    jetGronwallBound C T A B n ≤ jetGronwallBound C T A B (n + 1) := le_max_left _ _

/-- Each new constant also includes the top-order Gronwall bound. -/
theorem gronwallBound_le_jetGronwallBound (C T A B : ℝ) (n : ℕ) :
    gronwallBound B (12 * C * A ^ 2)
      (4 * 3 ^ (n + 1) * C * jetGronwallBound C T A B n ^ 3) T ≤
        jetGronwallBound C T A B (n + 1) := le_max_right _ _

end WaveTurbulence.WKEL2
