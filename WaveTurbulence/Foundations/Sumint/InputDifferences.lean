/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.AffinePredecessor
import Mathlib.Tactic

/-!
# Input variables are differences of localized affine variables

This module consumes the exact coefficient version of hypothesis (iii).
It derives the vector identity needed to insert input cutoffs in Step 1.
-/

public section

open Finset

namespace WaveTurbulence.Sumint

/-- Coefficient row of one of the primary, alternative, or external variables. -/
@[expose] def choiceRowT {d : ℕ} (D : SumintDatum d)
    (z : D.S.VIdx ⊕ D.S.VIdx ⊕ Fin 4) : D.S.VIdx → ℤ := match z with
  | .inl w => D.T₁ w
  | .inr (.inl w) => D.T₂ w
  | .inr (.inr _) => 0

/-- External coefficient row of the same variable. -/
@[expose] def choiceRowH {d : ℕ} (D : SumintDatum d)
    (z : D.S.VIdx ⊕ D.S.VIdx ⊕ Fin 4) : Fin 4 → ℤ := match z with
  | .inl w => D.H₁ w
  | .inr (.inl w) => D.H₂ w
  | .inr (.inr c) => Pi.single c 1

/-- The literal vector selected from the three source families. -/
@[expose] noncomputable def choiceVector {d : ℕ} (D : SumintDatum d) (L : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (E : Fin 4 → Mom d)
    (z : D.S.VIdx ⊕ D.S.VIdx ⊕ Fin 4) : Mom d := match z with
  | .inl w => D.kVec L x E w
  | .inr (.inl w) => D.ℓVec L x E w
  | .inr (.inr c) => E c

/-- Each selected variable has its advertised integer affine rows. -/
theorem choiceVector_eq_rows {d : ℕ} (D : SumintDatum d) (L : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (E : Fin 4 → Mom d)
    (z : D.S.VIdx ⊕ D.S.VIdx ⊕ Fin 4) :
    choiceVector D L x E z = (∑ j, choiceRowT D z j • latticePoint L (x j)) +
      ∑ c, choiceRowH D z c • E c := by
  classical
  rcases z with w | w | c
  · exact kVec_eq_integerAffineMap D L x E w
  · exact lVec_eq_integerAffineMap D L x E w
  · simp [choiceVector, choiceRowT, choiceRowH, Pi.single_apply]

/-- The exact admissibility premise gives an actual difference identity for every input. -/
theorem input_is_choice_difference {d : ℕ} (D : SumintDatum d) {A L γ η : ℝ}
    {Dsteps : ℕ} (hD : D.Admissible A L γ η Dsteps)
    (x : D.S.VIdx → Fin d → ℤ) (E : Fin 4 → Mom d) (v : D.S.VIdx) :
    ∃ a b, latticePoint L (x v) = choiceVector D L x E a - choiceVector D L x E b := by
  classical
  obtain ⟨a, b, hT, hH⟩ := hD.2.2.2.1 v
  change (∀ j, choiceRowT D a j - choiceRowT D b j = if j = v then 1 else 0) at hT
  change (∀ c, choiceRowH D a c - choiceRowH D b c = 0) at hH
  refine ⟨a, b, ?_⟩
  rw [choiceVector_eq_rows, choiceVector_eq_rows]
  have hh :
      ((∑ j, choiceRowT D a j • latticePoint L (x j)) + ∑ c, choiceRowH D a c • E c) -
        ((∑ j, choiceRowT D b j • latticePoint L (x j)) + ∑ c, choiceRowH D b c • E c) =
      (∑ j, (choiceRowT D a j - choiceRowT D b j) • latticePoint L (x j)) +
        ∑ c, (choiceRowH D a c - choiceRowH D b c) • E c := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel
  rw [hh]
  simp [hT, hH]

end WaveTurbulence.Sumint
