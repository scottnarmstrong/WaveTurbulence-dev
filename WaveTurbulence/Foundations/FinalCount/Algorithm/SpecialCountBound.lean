/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBStatistics
public import WaveTurbulence.Foundations.FinalCount.Degen.BondDeletion
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! # The source special-bond count is bounded by twice V3 -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Each special outgoing bond starts at a degree-three atom, which has
at most two outgoing bonds by the molecule axiom. -/
theorem special_count_le_two_degreeThree (M : Molecule V D) (hM : M.IsMolecule) :
    (appbSpecialBonds M).card ≤ 2*(appbDegreeAtoms M 3).card := by
  classical
  have hm : ∀ x ∈ appbSpecialBonds M,M.atom x ∈ appbDegreeAtoms M 3 := by
    intro x hx
    exact mem_filter.mpr ⟨M.atom_mem x,(mem_filter.mp hx).2.2.1⟩
  rw [card_eq_sum_card_fiberwise hm]
  calc
    _ ≤ ∑ v ∈ appbDegreeAtoms M 3,2 := by
      apply sum_le_sum
      intro v hv
      have hs : (appbSpecialBonds M).filter (fun x => M.atom x = v) ⊆ Degen.bondsOutAt M v := by
        intro x hx
        obtain ⟨hx,ha⟩ := mem_filter.mp hx
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2.1⟩,ha⟩
      exact (card_le_card hs).trans ((Degen.card_bondsOutAt M v).le.trans (hM.1 v (mem_filter.mp hv).1).1)
    _ = _ := by simp only [sum_const,nsmul_eq_mul,mul_comm,Nat.cast_id]

end WaveTurbulence.Mole.AppbAlgorithm
