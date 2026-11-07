/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBTripleOrdering
import Mathlib.Tactic

/-! # Degree caps on the boundary triple of a degree-three/four double pair -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole

/-- Two shared internal labels cancel with opposite signs. The remaining
three boundary signs cannot agree, by the caps at the original atoms. -/
theorem appb_triple_quad_boundary_signs (σ : Fin 5 → ℤˣ) (a : ℤˣ)
    (hfirst : ¬(σ 0 = a ∧ σ 1 = a ∧ σ 2 = a))
    (hsecond0 : ¬(-σ 0 = a ∧ σ 3 = a ∧ σ 4 = a))
    (hsecond1 : ¬(-σ 1 = a ∧ σ 3 = a ∧ σ 4 = a)) :
    ¬(σ 2 = a ∧ σ 3 = a ∧ σ 4 = a) := by
  rintro ⟨h2,h3,h4⟩
  have h0 : -σ 0 ≠ a := fun h => hsecond0 ⟨h,h3,h4⟩
  have h1 : -σ 1 ≠ a := fun h => hsecond1 ⟨h,h3,h4⟩
  have hσ0 : σ 0 = a := by
    have hh := appb_units_eq_neg_of_ne _ _ h0
    simpa only [neg_neg] using hh.symm
  have hσ1 : σ 1 = a := by
    have hh := appb_units_eq_neg_of_ne _ _ h1
    simpa only [neg_neg] using hh.symm
  exact hfirst ⟨hσ0,hσ1,h2⟩

end WaveTurbulence.Mole
