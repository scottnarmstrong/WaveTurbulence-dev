/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Logic.Equiv.Sum

/-!
# Finite products over unchanged factor fibers

Coarsening only regroups the original factors. The sigma-fiber
coordinate equivalence gives the exact finite product identity,
including empty coarse fibers.
-/

@[expose] public section
set_option autoImplicit false

open scoped BigOperators Classical

namespace WaveTurbulence.SumintPar

/-- Regroup a finite product over the unchanged subtype fibers of any map. -/
@[to_additive /-- Regroup a finite sum over the unchanged subtype fibers of any map. -/]
theorem prod_fiber_subtype {A B M : Type*} [Fintype A] [Fintype B] [CommMonoid M]
    (g : A → B) [∀ b : B, Fintype {a : A // g a = b}] (f : A → M) :
    (∏ b : B, ∏ a : {a : A // g a = b}, f a.1) = ∏ a : A, f a := by
  have he := (Equiv.sigmaFiberEquiv g).prod_comp f
  simpa only [Fintype.prod_sigma,Equiv.sigmaFiberEquiv_apply] using he

/-- A fiber product is the unrestricted product with the complementary factors replaced by one. -/
theorem prod_fiber_subtype_eq_ite {A B M : Type*} [Fintype A] [DecidableEq B] [CommMonoid M]
    (g : A → B) (b : B) [Fintype {a : A // g a = b}] (f : A → M) :
    (∏ a : {a : A // g a = b}, f a.1) = ∏ a : A, if g a = b then f a else 1 := by
  rw [← Finset.prod_filter]
  exact (Finset.prod_subtype (Finset.univ.filter (fun a => g a = b))
    (fun a => by simp only [Finset.mem_filter,Finset.mem_univ,true_and]) f).symm

end WaveTurbulence.SumintPar
