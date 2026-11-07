/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card

/-!
# Separating a distinguished first pair from its finite remainder

The complement subtype avoids changing any source pair index. Both the
product and discrepancy sum split at the same distinguished index,
and the remainder has exactly one fewer element.
-/

@[expose] public section
set_option autoImplicit false

open scoped BigOperators

namespace WaveTurbulence.SumintPar

/-- Split a finite product at a distinguished index without renumbering its remainder. -/
@[to_additive /-- Split a finite sum at the same distinguished index as its product. -/]
theorem prod_first_rest {ι α : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid α]
    (a : ι) (f : ι → α) :
    (∏ i, f i) = f a*(∏ i : {i : ι // i ≠ a}, f i) := by
  rw [← Finset.prod_subtype (Finset.univ.erase a) (by intro i; simp) f]
  exact (Finset.mul_prod_erase Finset.univ f (Finset.mem_univ a)).symm

/-- The unchanged-index remainder contains exactly one fewer source pair. -/
theorem card_first_rest {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) :
    Fintype.card {i : ι // i ≠ a} = Fintype.card ι-1 := by
  rw [Fintype.card_subtype_compl,Fintype.card_subtype_eq]

end WaveTurbulence.SumintPar
