/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LatticeCoordinates

/-! # Support of the exact Wick-factor correction

DH23 end of Prop6.1, with F62's square retained. Replacing the full
factor by1 changes the summand only on a union of coordinate-zero sets.
-/

public section
namespace WaveTurbulence.RegAsymp
open Links Finset

/-- A single squared link factor is either0 or1. -/
theorem epsXY_sq_cases {d : ℕ} (x y : Fin d → ℤ) :
    epsXY x y ^ 2 = 0 ∨ epsXY x y ^ 2 = 1 := by
  unfold epsXY
  split_ifs <;> norm_num

/-- The product of squared factors is still either0 or1. -/
theorem prod_epsXY_sq_cases {d n : ℕ} (θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ)) :
    (∏ j, epsXY (θ j).1 (θ j).2 ^ 2) = 0 ∨ (∏ j, epsXY (θ j).1 (θ j).2 ^ 2) = 1 := by
  have h (S : Finset (Fin n)) : (∏ j ∈ S, epsXY (θ j).1 (θ j).2 ^ 2) = 0 ∨
      (∏ j ∈ S, epsXY (θ j).1 (θ j).2 ^ 2) = 1 := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert j S hj ih =>
      rw [prod_insert hj]
      rcases epsXY_sq_cases (θ j).1 (θ j).2 with he | he <;>
        rcases ih with hi | hi <;> simp [he,hi]
  exact h univ

end WaveTurbulence.RegAsymp
