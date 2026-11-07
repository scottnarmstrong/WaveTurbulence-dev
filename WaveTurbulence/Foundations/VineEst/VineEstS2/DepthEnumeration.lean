/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Prod.Lex.Basic

/-! # Finite node enumeration with descendants before their parents -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2

/-- Any finite family can be enumerated in decreasing depth. The auxiliary
finite label breaks ties, and imposes no geometric hypothesis. -/
theorem exists_depth_enumeration (α : Type*) [Fintype α] (depth : α → ℕ) :
    ∃ e : α ≃ Fin (Fintype.card α), ∀ a b, depth a < depth b → e b < e a := by
  classical
  let e := Fintype.equivFin α
  let key : α → (OrderDual ℕ) ×ₗ Fin (Fintype.card α) := fun a => toLex (depth a,e a)
  have hkey : Function.Injective key := by
    intro a b hab
    apply e.injective
    exact congrArg (fun q : (OrderDual ℕ) ×ₗ Fin (Fintype.card α) => (ofLex q).2) hab
  let : LinearOrder α := LinearOrder.lift' key hkey
  let o := Fintype.orderIsoFinOfCardEq α rfl
  refine ⟨o.symm.toEquiv,?_⟩
  intro a b hab
  apply o.symm.strictMono
  change key b < key a
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hab)

end WaveTurbulence.VineEstS2
