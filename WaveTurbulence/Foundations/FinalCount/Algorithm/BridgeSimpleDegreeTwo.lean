/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ErasedBondMultiplicity
public import WaveTurbulence.Foundations.FinalCount.Algorithm.SimpleDegreeTwoLocalEdit
public import WaveTurbulence.Foundations.FinalCount.AppBBridgeGraphEffects
import Mathlib.Tactic

/-! # Actual V2-star increments at bridge removal -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

open Classical in
theorem bridge_simpleDegreeTwo_difference (M : Molecule V D) (e : D) (hb : Degen.IsBridge M e) :
    ((simpleDegreeTwoAtoms (eraseBond M e)).card : ℤ)-(simpleDegreeTwoAtoms M).card =
      ((if SimpleDegreeTwo (eraseBond M e) (M.atom e) then (1 : ℤ) else 0)-
        (if SimpleDegreeTwo M (M.atom e) then 1 else 0))+
      ((if SimpleDegreeTwo (eraseBond M e) (M.atom (M.mate e)) then 1 else 0)-
        (if SimpleDegreeTwo M (M.atom (M.mate e)) then 1 else 0)) := by
  classical
  have hS : ({M.atom e,M.atom (M.mate e)} : Finset V) ⊆ M.atoms := by
    intro a ha
    rcases mem_insert.mp ha with rfl | ha
    · exact M.atom_mem _
    · exact mem_singleton.mp ha ▸ M.atom_mem _
  have hout : ∀ a ∈ M.atoms,a ∉ ({M.atom e,M.atom (M.mate e)} : Finset V) →
      (SimpleDegreeTwo (eraseBond M e) a ↔ SimpleDegreeTwo M a) := by
    intro a ha hn
    have hn1 : M.atom e ≠ a := by intro h; exact hn (by simp [h])
    have hn2 : M.atom (M.mate e) ≠ a := by intro h; exact hn (by simp [h])
    exact eraseBond_simpleDegreeTwo_iff_of_not_endpoint M e hn1 hn2
  rw [simpleDegreeTwo_difference_of_local_edit M (eraseBond M e) rfl _ hS hout,
    sum_pair (appb_bridge_endpoints_distinct M e hb)]

open Classical in
/-- Source BR333 creates only the possible two new simple degree-two atoms. -/
theorem bridge333_simpleDegreeTwo_difference (M : Molecule V D) (e : D)
    (hb : Degen.IsBridge M e) (h1 : M.deg (M.atom e) = 3)
    (h2 : M.deg (M.atom (M.mate e)) = 3) :
    ((simpleDegreeTwoAtoms (eraseBond M e)).card : ℤ)-(simpleDegreeTwoAtoms M).card =
      (if SimpleDegreeTwo (eraseBond M e) (M.atom e) then (1 : ℤ) else 0)+
      (if SimpleDegreeTwo (eraseBond M e) (M.atom (M.mate e)) then 1 else 0) := by
  classical
  have hn1 : ¬SimpleDegreeTwo M (M.atom e) := fun h => by have hh := h.1; omega
  have hn2 : ¬SimpleDegreeTwo M (M.atom (M.mate e)) := fun h => by have hh := h.1; omega
  rw [bridge_simpleDegreeTwo_difference M e hb]
  simp only [hn1,hn2,ite_false,sub_zero]

theorem bridge333_simpleDegreeTwo_nondecrease (M : Molecule V D) (e : D)
    (hb : Degen.IsBridge M e) (h1 : M.deg (M.atom e) = 3)
    (h2 : M.deg (M.atom (M.mate e)) = 3) :
    (simpleDegreeTwoAtoms M).card ≤ (simpleDegreeTwoAtoms (eraseBond M e)).card := by
  classical
  have hh := bridge333_simpleDegreeTwo_difference M e hb h1 h2
  split_ifs at hh <;> omega

/-- The equality condition is a predicate on the actual post stars; the
special-bond characterization is a separate geometric theorem. -/
theorem bridge333_simpleDegreeTwo_eq_iff (M : Molecule V D) (e : D)
    (hb : Degen.IsBridge M e) (h1 : M.deg (M.atom e) = 3)
    (h2 : M.deg (M.atom (M.mate e)) = 3) :
    (simpleDegreeTwoAtoms (eraseBond M e)).card = (simpleDegreeTwoAtoms M).card ↔
      ¬SimpleDegreeTwo (eraseBond M e) (M.atom e) ∧
      ¬SimpleDegreeTwo (eraseBond M e) (M.atom (M.mate e)) := by
  classical
  constructor
  · intro heq
    have hz : ((simpleDegreeTwoAtoms (eraseBond M e)).card : ℤ)-(simpleDegreeTwoAtoms M).card = 0 := by
      rw [heq,sub_self]
    rw [bridge333_simpleDegreeTwo_difference M e hb h1 h2] at hz
    by_cases hn1 : SimpleDegreeTwo (eraseBond M e) (M.atom e) <;>
      by_cases hn2 : SimpleDegreeTwo (eraseBond M e) (M.atom (M.mate e))
    all_goals simp only [hn1,hn2,ite_true,ite_false] at hz
    all_goals try norm_num at hz
    exact ⟨hn1,hn2⟩
  · intro hn
    have hh := bridge333_simpleDegreeTwo_difference M e hb h1 h2
    simp only [hn.1,hn.2,ite_false,add_zero] at hh
    exact_mod_cast (sub_eq_zero.mp hh)

end WaveTurbulence.Mole.AppbAlgorithm
