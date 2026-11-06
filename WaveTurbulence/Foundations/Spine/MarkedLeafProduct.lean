/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
/-! A marked remainder leaf retains its smallness factor in the multilinear seminorm product. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset

/-- A single marked small input suffices; all other inputs retain their ordinary bounds. -/
theorem prod_le_marked_factor {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f g : ι → NNReal) (ε : NNReal) (h : ∀ i ∈ s, f i ≤ g i)
    (hmark : ∃ a ∈ s, f a ≤ ε * g a) :
    (∏ i ∈ s, f i) ≤ ε * ∏ i ∈ s, g i := by
  obtain ⟨a, ha, hsmall⟩ := hmark
  calc
    _ = (∏ i ∈ s.erase a, f i) * f a := (prod_erase_mul s f ha).symm
    _ ≤ (∏ i ∈ s.erase a, g i) * (ε * g a) := by
      exact mul_le_mul' (prod_le_prod (fun i hi => h i (mem_erase.mp hi).2)) hsmall
    _ = ε * ∏ i ∈ s, g i := by rw [← prod_erase_mul s g ha]; ac_rfl

end WaveTurbulence.LGSpine
