/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.FiniteOrderCutoff
/-! Conditional finite order sums equal the exact-order source subtype finsums. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem sum_subtype_ite_order_eq_finsum {α : Type*} (P : α → Prop) [Fintype {a : α // P a}]
    (order : α → ℕ) (f : α → ℂ) (N : ℕ) :
    (∑ a : {a : α // P a}, if order a.1 = N then f a.1 else 0) =
      ∑ᶠ a : {a : α // P a ∧ order a = N}, f a.1 := by
  classical
  let e : {a : {a : α // P a} // order a.1 = N} ≃ {a : α // P a ∧ order a = N} :=
    { toFun := fun a => ⟨a.1.1, a.1.2, a.2⟩
      invFun := fun a => ⟨⟨a.1, a.2.1⟩, a.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hsum := (finsum_eq_sum_of_fintype (fun a : {a : α // P a} =>
    if order a.1 = N then f a.1 else 0)).symm
  have hi : (∑ᶠ a : {a : α // P a}, if order a.1 = N then f a.1 else 0) =
      ∑ᶠ (a : {a : α // P a}) (_ : order a.1 = N), f a.1 := by
    apply finsum_congr
    intro a
    rw [finsum_eq_if]
  have hsub := (finsum_subtype_eq_finsum_cond (f := fun a : {a : α // P a} => f a.1)
    (fun a => order a.1 = N)).symm
  exact hsum.trans (hi.trans (hsub.trans (finsum_comp_equiv e (f := fun a => f a.1))))

end WaveTurbulence.Induct
