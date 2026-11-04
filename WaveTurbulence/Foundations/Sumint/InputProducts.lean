/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.InputFactors

/-!
# Exact coordinate-product decomposition into source input factors

This identity reindexes a finite product through the actual slot
bijection. It applies to cutoffs and to independent modulation characters
before the oscillatory terms are grouped into their standard sums.
-/

public section

open Finset

namespace WaveTurbulence.Sumint

/-- Every coordinate product is exactly the product of its linear, pair
and normal input factors. -/
theorem prod_source_input_slots (S : SumintShape) {α M : Type*} [CommMonoid M]
    (F : S.VIdx → α → M) (x : S.VIdx → α) :
    (∏ v, F v (x v)) =
      (∏ i : Fin S.I, F (S.x0Slot i) (x (S.x0Slot i))) *
      (∏ p : Σ i : Fin S.I, Fin (S.m i),
        F (S.xSlot p.1 p.2) (x (S.xSlot p.1 p.2))*F (S.ySlot p.1 p.2) (x (S.ySlot p.1 p.2))) *
      (∏ i : {i : Fin S.I // S.nor i = true}, ∏ j : Fin 3,
        F (S.uSlot i.1 i.2 j) (x (S.uSlot i.1 i.2 j))) := by
  calc
    _ = ∏ u : S.TVar, F (inputTimeSlot S u) (x (inputTimeSlot S u)) :=
      ((timeVectorEquiv S).prod_comp (fun v => F v (x v))).symm
    _ = _ := by
      simp only [Fintype.prod_sum_type,Fintype.prod_sigma,inputTimeSlot,
        Fin.prod_univ_succ,SumintShape.x0Slot,SumintShape.xSlot,SumintShape.ySlot,
        SumintShape.uSlot,Finset.prod_mul_distrib]
      ac_rfl

end WaveTurbulence.Sumint
