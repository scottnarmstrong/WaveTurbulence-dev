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

theorem prod_epsXY_sq_eq_one_of_nonzero {d n : ℕ}
    (θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ))
    (hθ : ∀ j, (θ j).1 ≠ 0 ∧ (θ j).2 ≠ 0) :
    (∏ j, epsXY (θ j).1 (θ j).2 ^ 2) = 1 := by
  apply prod_eq_one
  intro j _
  have hxy : (θ j).2 ≠ 0 ∧ (θ j).1 ≠ 0 := ⟨(hθ j).2,(hθ j).1⟩
  simp only [epsXY,ite_eq_left hxy,one_pow]

/-- The difference has pointwise size at most1, not an exponentially
large factor. -/
theorem abs_wick_difference_le_one {d n : ℕ}
    (θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ)) :
    |(∏ j, epsXY (θ j).1 (θ j).2 ^ 2) - 1| ≤ 1 := by
  rcases prod_epsXY_sq_cases θ with h | h <;> rw [h] <;> norm_num

/-- Nonzero correction forces at least one zero coordinate. -/
theorem wick_difference_supported {d n : ℕ}
    (θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ))
    (h : (∏ j, epsXY (θ j).1 (θ j).2 ^ 2) - 1 ≠ 0) :
    ∃ j, (θ j).1 = 0 ∨ (θ j).2 = 0 := by
  by_contra hn
  push Not at hn
  exact h (by rw [prod_epsXY_sq_eq_one_of_nonzero θ hn,sub_self])

end WaveTurbulence.RegAsymp
