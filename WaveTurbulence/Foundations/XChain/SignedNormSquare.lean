/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SignedComposition
public import WaveTurbulence.Foundations.XChain.CumulantDoubleton
/-! The squared norm of a signed product is the actual doubled signed product. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem zpowSign_neg_eq_conj (ζ : ℤˣ) (z : ℂ) :
    zpowSign (-ζ) z = (starRingEnd ℂ) (zpowSign ζ z) := by
  rcases Int.units_eq_one_or ζ with rfl | rfl <;> simp [zpowSign]

theorem signed_product_norm_sq {ι : Type*} [Fintype ι] (ζ : ι → ℤˣ) (z : ι → ℂ) :
    (‖∏ j, zpowSign (ζ j) (z j)‖ ^ 2 : ℂ) =
      ∏ x : Fin 2 × ι, zpowSign (if x.1 = 0 then ζ x.2 else -ζ x.2) (z x.2) := by
  classical
  rw [Fintype.prod_prod_type, Fin.prod_univ_two]
  simp only [ite_true, show (1 : Fin 2) ≠ 0 from by decide, ite_false, zpowSign_neg_eq_conj, ← map_prod]
  exact (Complex.mul_conj' _).symm

end WaveTurbulence.Induct
