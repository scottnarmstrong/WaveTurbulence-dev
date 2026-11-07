/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBPhysicalPairFine
import Mathlib.Tactic

/-! # Normalizing the two actual source orientation signs -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole

/-- Multiplying by the first orientation sign puts every two-bond momentum
equation in the exact basiccount(1) form. -/
theorem appb_signed_pair_momentum {E : Type*} [AddCommGroup E]
    (σ τ : ℤˣ) (x y c : E) (h : (σ : ℤ) • x+(τ : ℤ) • y = c) :
    x+((σ⁻¹*τ : ℤˣ) : ℤ) • y = ((σ⁻¹ : ℤˣ) : ℤ) • c := by
  rcases Int.units_eq_one_or σ with rfl | rfl
  · simpa using h
  · have hh := congrArg Neg.neg h
    simpa [neg_add,add_comm] using hh

/-- The same normalization retains the absolute energy tolerance exactly. -/
theorem appb_signed_pair_energy (σ τ : ℤˣ) (a b β W : ℝ)
    (h : |(σ : ℤ)*a+(τ : ℤ)*b-β| ≤ W) :
    |a+((σ⁻¹*τ : ℤˣ) : ℤ)*b-((σ⁻¹ : ℤˣ) : ℤ)*β| ≤ W := by
  rcases Int.units_eq_one_or σ with rfl | rfl
  · simpa using h
  · have he : |a+(((-1 : ℤˣ)⁻¹*τ : ℤˣ) : ℤ)*b-(((-1 : ℤˣ)⁻¹ : ℤˣ) : ℤ)*β| =
        |(-1 : ℤ)*a+(τ : ℤ)*b-β| := by
      rw [← abs_neg]
      congr 1
      simp
      ring
    rw [he]
    exact h

end WaveTurbulence.Mole
