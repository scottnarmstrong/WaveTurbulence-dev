/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.StarMultiplicity
import Mathlib.Tactic

/-! # Distinct star neighbors are equivalent to single incident bonds -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace Star
variable {M : Molecule V D} {v : V} {k : ℕ} (st : Star M v k)

theorem neighbor_injective_of_single (h : ∀ i,M.bondsBetween v (st.neighbor i) ≤ 1) :
    Function.Injective st.neighbor := by
  classical
  intro i j hij
  by_contra hne
  have hh : 1 < (univ.filter fun t : Fin k => st.neighbor t = st.neighbor i).card := by
    apply one_lt_card.mpr
    exact ⟨i,mem_filter.mpr ⟨mem_univ _,rfl⟩,
      j,mem_filter.mpr ⟨mem_univ _,hij.symm⟩,hne⟩
  have hi := h i
  rw [st.bondsBetween_eq_neighbor_count] at hi
  omega

theorem bondsBetween_neighbor_eq_one (hinj : Function.Injective st.neighbor) (i : Fin k) :
    M.bondsBetween v (st.neighbor i) = 1 := by
  classical
  rw [st.bondsBetween_eq_neighbor_count]
  have hf : (univ.filter fun t : Fin k => st.neighbor t = st.neighbor i) = {i} := by
    ext j
    simp only [mem_filter,mem_univ,true_and,mem_singleton]
    exact ⟨fun h => hinj h,fun h => congrArg st.neighbor h⟩
  rw [hf,card_singleton]

end Star
end WaveTurbulence.Mole.AppbAlgorithm
