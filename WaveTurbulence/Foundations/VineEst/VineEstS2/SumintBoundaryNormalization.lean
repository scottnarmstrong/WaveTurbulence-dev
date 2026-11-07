/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.PhysicalPredecessor
public import Mathlib.Logic.Equiv.Basic

/-! # The source signed boundary constraint in sumint's exact convention -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2

/-- The physical upper and excluded-child momenta are swapped precisely
when the upper sign is positive. The lower positive/negative order is fixed. -/
def sumintBoundaryPermutation (ζ : ℤˣ) : Fin 4 ≃ Fin 4 :=
  if ζ = 1 then Equiv.swap 0 1 else Equiv.refl _

def sumintBoundary {E : Type*} (ζ : ℤˣ) (β : Fin 4 → E) : Fin 4 → E :=
  fun c => β (sumintBoundaryPermutation ζ c)

theorem sumintBoundary_lower {E : Type*} (ζ : ℤˣ) (β : Fin 4 → E) :
    sumintBoundary ζ β 2 = β 2 ∧ sumintBoundary ζ β 3 = β 3 := by
  unfold sumintBoundary sumintBoundaryPermutation
  split_ifs <;> simp only [Equiv.refl_apply,Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 4) ≠ 0)
    (by decide : (2 : Fin 4) ≠ 1),Equiv.swap_apply_of_ne_of_ne (by decide : (3 : Fin 4) ≠ 0)
    (by decide : (3 : Fin 4) ≠ 1),and_self]

/-- Exact frozen sumint momentum relation, including the diagonal case. -/
theorem sumintBoundary_momentum {E : Type*} [AddCommGroup E] (ζ : ℤˣ) (β : Fin 4 → E)
    (hβ : (ζ : ℤ) • (β 0-β 1) = β 2-β 3) :
    sumintBoundary ζ β 0-sumintBoundary ζ β 1 = sumintBoundary ζ β 3-sumintBoundary ζ β 2 := by
  rcases Int.units_eq_one_or ζ with rfl | rfl
  · simp only [Units.val_one,one_smul] at hβ
    simpa only [sumintBoundary,sumintBoundaryPermutation,ite_true,Equiv.swap_apply_left,
      Equiv.swap_apply_right,Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 4) ≠ 0)
      (by decide : (2 : Fin 4) ≠ 1),Equiv.swap_apply_of_ne_of_ne (by decide : (3 : Fin 4) ≠ 0)
      (by decide : (3 : Fin 4) ≠ 1),neg_sub] using congrArg (fun x : E => -x) hβ
  · simp only [Units.val_neg,Units.val_one,neg_one_smul] at hβ
    have hn : (-1 : ℤˣ) ≠ 1 := by decide
    simpa only [sumintBoundary,sumintBoundaryPermutation,hn,ite_false,Equiv.refl_apply,neg_neg,neg_sub]
      using congrArg (fun x : E => -x) hβ

theorem sumintBoundary_gap {E : Type*} [AddCommGroup E] (ζ : ℤˣ) (β : Fin 4 → E)
    (hβ : (ζ : ℤ) • (β 0-β 1) = β 2-β 3) :
    sumintBoundary ζ β 0-sumintBoundary ζ β 1 = -(β 2-β 3) := by
  rw [sumintBoundary_momentum ζ β hβ,(sumintBoundary_lower ζ β).1,(sumintBoundary_lower ζ β).2,neg_sub]

/-- Source and sumint diagonal/nonzero cases are exactly the same. -/
theorem sumintBoundary_ne_iff {E : Type*} [AddCommGroup E] (ζ : ℤˣ) (β : Fin 4 → E)
    (hβ : (ζ : ℤ) • (β 0-β 1) = β 2-β 3) :
    sumintBoundary ζ β 0 ≠ sumintBoundary ζ β 1 ↔ β 2 ≠ β 3 := by
  have he : sumintBoundary ζ β 0 = sumintBoundary ζ β 1 ↔ β 2 = β 3 := by
    rw [← sub_eq_zero,sumintBoundary_gap ζ β hβ,neg_eq_zero,sub_eq_zero]
  exact not_congr he

/-- All source parameters remain in the same physical lattice coset after
this fixed finite permutation. -/
theorem sumintBoundary_mem {E : Type*} (ζ : ℤˣ) (β : Fin 4 → E) (P : E → Prop)
    (hβ : ∀ c, P (β c)) : ∀ c, P (sumintBoundary ζ β c) :=
  fun c => hβ (sumintBoundaryPermutation ζ c)

end WaveTurbulence.VineEstS2
