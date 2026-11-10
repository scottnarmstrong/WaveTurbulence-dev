/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.RelativeFactorIdentities
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-! # Pointwise factorization of the actual full source kernel integrand -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

open scoped Classical in
theorem mask_mul_prod {ι : Type*} [Fintype ι] (A : Prop) (B : ι → Prop) (a : ℂ) (b : ι → ℂ) :
    (if A ∧ ∀ i, B i then a * ∏ i, b i else 0) =
      (if A then a else 0) * ∏ i, if B i then b i else 0 := by
  classical
  rw [Fintype.prod_ite_zero]
  by_cases ha : A <;> by_cases hb : ∀ i, B i <;> simp [ha,hb]

end WaveTurbulence.RegRed
