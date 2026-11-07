/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBTripleOrdering
import Mathlib.Tactic

/-! # Three orientation cases relative to a distinguished shared bond -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole

theorem appb_three_sign_cases (σ : Fin 3 → ℤˣ)
    (hplus : ¬∀ i,σ i = 1) (hminus : ¬∀ i,σ i = -1) :
    (σ 1 = σ 2 ∧ σ 1 ≠ σ 0) ∨ (σ 0 = σ 1 ∧ σ 0 ≠ σ 2) ∨ (σ 0 = σ 2 ∧ σ 0 ≠ σ 1) := by
  by_cases h01 : σ 0 = σ 1
  · right; left
    refine ⟨h01,?_⟩
    intro h02
    rcases Int.units_eq_one_or (σ 0) with h | h
    · apply hplus
      intro i
      fin_cases i <;> simp_all
    · apply hminus
      intro i
      fin_cases i <;> simp_all
  · by_cases h02 : σ 0 = σ 2
    · exact Or.inr (Or.inr ⟨h02,h01⟩)
    · exact Or.inl ⟨(appb_units_eq_neg_of_ne _ _ h01).trans (appb_units_eq_neg_of_ne _ _ h02).symm,Ne.symm h01⟩

end WaveTurbulence.Mole
