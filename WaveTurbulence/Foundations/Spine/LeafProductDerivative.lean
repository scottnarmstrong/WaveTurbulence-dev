/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoordinateDerivativeNorm
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
/-! Coordinate differentiation of a finite leaf product is an exact sum of single-leaf updates. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

theorem partialMom_finsetProd {I : Type*} [DecidableEq I] {d : ℕ}
    (s : Finset I) (f : I → Mom d → ℂ) (j : Fin d) (x : Mom d)
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) :
    partialMom j (fun y => ∏ i ∈ s, f i y) x =
      ∑ i ∈ s, (∏ a ∈ s.erase i, f a x) * partialMom j (f i) x := by
  unfold partialMom
  have he : (fun y => ∏ i ∈ s, f i y) = (∏ i ∈ s, f i ·) := rfl
  rw [he, fderiv_finsetProd hf]
  simp only [_root_.sum_apply, smul_apply, smul_eq_mul]

theorem partialMom_prod_single_leaf {I : Type*} [DecidableEq I] {d : ℕ}
    (s : Finset I) (f : I → Mom d → ℂ) (j : Fin d) (x : Mom d)
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) :
    partialMom j (fun y => ∏ i ∈ s, f i y) x =
      ∑ i ∈ s, ∏ a ∈ s, Function.update f i (partialMom j (f i)) a x := by
  rw [partialMom_finsetProd s f j x hf]
  apply sum_congr rfl
  intro i hi
  have he : (fun a => Function.update f i (partialMom j (f i)) a x) =
      Function.update (fun a => f a x) i (partialMom j (f i) x) := by
    funext a
    by_cases ha : a = i
    · subst a
      simp only [Function.update_self]
    · simp only [Function.update_of_ne ha]
  rw [show (∏ a ∈ s, Function.update f i (partialMom j (f i)) a x) =
      ∏ a ∈ s, Function.update (fun a => f a x) i (partialMom j (f i) x) a from
        congrArg (fun g : I → ℂ => ∏ a ∈ s, g a) he]
  rw [prod_update_of_mem hi]
  rw [sdiff_singleton_eq_erase]
  exact mul_comm _ _

end WaveTurbulence.LGSpine
