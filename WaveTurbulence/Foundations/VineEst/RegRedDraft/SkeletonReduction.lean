/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.ReducedLatticeFubini
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.FiniteIndependentSums
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.KernelPrefactors

/-! # TARGET regred: reduction of the actual garden kernel to its skeleton -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton MeasureTheory

theorem indicator_mul_right_apply {α : Type*} (A : Set α) (f g : α → ℂ) (x : α) :
    A.indicator f x * g x = A.indicator (fun y => f y*g y) x := by
  by_cases hx : x ∈ A
  · simp only [Set.indicator_of_mem hx]
  · simp only [Set.indicator_of_notMem hx,zero_mul]

end WaveTurbulence.RegRed
