/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBTripleOrdering
public import WaveTurbulence.Foundations.FinalCount.AppBTripleFrameConservation
import Mathlib.Tactic

/-! # Ordering an arbitrary signed three-label conservation equation -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset

theorem appb_ordered_signed_triple_momentum {E : Type*} [AddCommGroup E]
    (σ : Fin 3 → ℤˣ) (π : Equiv.Perm (Fin 3)) (hsame : σ (π 0) = σ (π 2))
    (hopp : σ (π 0) ≠ σ (π 1)) (q : Fin 3 → E) (c : E)
    (hc : ∑ j,(σ j : ℤ) • q j = c) :
    q (π 0)-q (π 1)+q (π 2) = (((σ (π 0))⁻¹ : ℤˣ) : ℤ) • c := by
  rw [appb_sum_fin_three_permutation π] at hc
  have hmid := appb_units_eq_neg_of_ne _ _ hopp
  apply appb_signed_triple_momentum (σ (π 0))
  simpa only [hmid,← hsame,Units.val_neg,neg_smul,sub_eq_add_neg] using hc

theorem appb_ordered_signed_triple_energy (σ : Fin 3 → ℤˣ) (π : Equiv.Perm (Fin 3))
    (hsame : σ (π 0) = σ (π 2)) (hopp : σ (π 0) ≠ σ (π 1)) (q : Fin 3 → ℝ) (β τ : ℝ)
    (hc : |(∑ j,(σ j : ℤ)*q j)-β| ≤ τ) :
    |q (π 0)-q (π 1)+q (π 2)-((((σ (π 0))⁻¹ : ℤˣ) : ℤ) : ℝ)*β| ≤ τ := by
  rw [appb_sum_fin_three_permutation π] at hc
  have hmid := appb_units_eq_neg_of_ne _ _ hopp
  apply appb_signed_triple_energy (σ (π 0))
  simpa only [hmid,← hsame,Units.val_neg,Int.cast_neg,neg_mul,sub_eq_add_neg] using hc

end WaveTurbulence.Mole
