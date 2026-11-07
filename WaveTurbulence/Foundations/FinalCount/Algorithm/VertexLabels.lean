/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBRealizations
public import Mathlib.Data.List.Nodup
import Mathlib.Tactic

/-! # One-based figure labels from a list of distinct actual atoms -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V : Type*}

/-- Values outside the figure's positive labels are immaterial. -/
def vertexLabels (xs : List V) (fallback : V) (i : ℕ) : V :=
  if hi : 1 ≤ i ∧ i ≤ xs.length then xs[i-1]'(by omega) else fallback

theorem vertexLabels_injective {xs : List V} (fallback : V) (hxs : xs.Nodup) :
    Set.InjOn (vertexLabels xs fallback) (Icc 1 xs.length : Finset ℕ) := by
  intro i hi j hj hij
  have hi' := mem_Icc.mp hi
  have hj' := mem_Icc.mp hj
  simp only [vertexLabels,dite_eq_left hi',dite_eq_left hj'] at hij
  have hh := hxs.getElem_inj_iff.mp hij
  omega

theorem vertexLabels_mem {xs : List V} (fallback : V) {i : ℕ}
    (hi : i ∈ Icc 1 xs.length) : vertexLabels xs fallback i ∈ xs := by
  have hi' := mem_Icc.mp hi
  simp only [vertexLabels,dite_eq_left hi']
  exact List.getElem_mem _

end WaveTurbulence.Mole.AppbAlgorithm
