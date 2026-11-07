/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBTriplePermutation
import Mathlib.Tactic

/-! # Ordering a signed triple while preserving its distinguished internal pair -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole

/-- Opposite first two signs allow the first free difference to remain
exactly the internal difference, up to sign. -/
theorem appb_internal_pair_order (σ : Fin 3 → ℤˣ) (h01 : σ 0 ≠ σ 1) :
    ∃ π : Equiv.Perm (Fin 3), σ (π 0) = σ (π 2) ∧ σ (π 0) ≠ σ (π 1) ∧
      ((π 0 = 0 ∧ π 1 = 1) ∨ (π 0 = 1 ∧ π 1 = 0)) := by
  by_cases h02 : σ 0 = σ 2
  · exact ⟨Equiv.refl _,h02,h01,Or.inl ⟨rfl,rfl⟩⟩
  · have h12 : σ 1 = σ 2 :=
      (appb_units_eq_neg_of_ne _ _ h01).trans (appb_units_eq_neg_of_ne _ _ h02).symm
    refine ⟨Equiv.swap 0 1,?_,?_,Or.inr ⟨by decide,by decide⟩⟩
    · have h2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
      simpa only [Equiv.swap_apply_left,h2] using h12
    · simpa using h01.symm

theorem appb_internal_pair_norm {E : Type*} [SeminormedAddCommGroup E]
    (π : Equiv.Perm (Fin 3))
    (hπ : (π 0 = 0 ∧ π 1 = 1) ∨ (π 0 = 1 ∧ π 1 = 0)) (q : Fin 3 → E) :
    ‖q (π 0)-q (π 1)‖ = ‖q 0-q 1‖ := by
  rcases hπ with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · rw [h0,h1]
  · rw [h0,h1,norm_sub_rev]

end WaveTurbulence.Mole
