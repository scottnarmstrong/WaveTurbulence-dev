/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.BoundedOrderEquiv
/-! Regrouping a finite bounded-order source sum by its exact total order. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem finsum_boundedOrder_eq_sum_orders {α : Type*} (P : α → Prop) (order : α → ℕ) (M : ℕ)
    (hFin : {a : α | P a ∧ order a ≤ M}.Finite) (f : α → ℂ) :
    (∑ᶠ a : {a : α // P a ∧ order a ≤ M}, f a.1) =
      ∑ n : Fin (M + 1), ∑ᶠ a : {a : α // P a ∧ order a = n.1}, f a.1 := by
  classical
  haveI : Finite {a : α // P a ∧ order a ≤ M} := hFin.to_subtype
  haveI : ∀ n : Fin (M + 1), Finite {a : α // P a ∧ order a = n.1} := fun n =>
    (hFin.subset (fun a h => ⟨h.1, h.2.trans_le (Nat.le_of_lt_succ n.2)⟩)).to_subtype
  letI : Fintype {a : α // P a ∧ order a ≤ M} := Fintype.ofFinite _
  letI : ∀ n : Fin (M + 1), Fintype {a : α // P a ∧ order a = n.1} := fun _ => Fintype.ofFinite _
  simp only [finsum_eq_sum_of_fintype]
  have he := Fintype.sum_equiv (boundedOrderEquiv P order M)
    (fun x => f x.2.1) (fun a => f a.1) (fun _ => rfl)
  exact he.symm.trans (Fintype.sum_sigma _)

end WaveTurbulence.Induct
