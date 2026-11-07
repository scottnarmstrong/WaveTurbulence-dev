/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBPairIncidence
public import WaveTurbulence.Foundations.FinalCount.AppBCutPair
import Mathlib.Tactic

/-! # The singleton two-bond cut at an actual degree-two atom -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbLocalPair
variable {M : Molecule V D} {P : AppbPattern} {r : AppbRealization M P} {v : V}
    (t : AppbLocalPair r v)

def singletonCut (hv : v ∈ r.removedAtoms) : AppbCutPair r {v} where
  subset_atoms := singleton_subset_iff.mpr (r.removedAtoms_subset hv)
  crossing := by
    intro x hx
    obtain ⟨hx,hh⟩ := mem_filter.mp hx
    apply mem_filter.mpr
    refine ⟨hx,?_⟩
    rcases hh with hh | hh
    · exact Or.inl ((mem_singleton.mp hh.1).symm ▸ hv)
    · exact Or.inr ((mem_singleton.mp hh.2).symm ▸ hv)
  first := t.first
  second := t.second
  distinct := t.distinct
  first_cross := by
    have hi := t.incidence_first
    by_cases ha : M.atom (r.edge t.first).val = v <;>
      by_cases hb : M.atom (M.mate (r.edge t.first).val) = v
    all_goals simp_all [appbIncidence]
  second_cross := by
    have hi := t.incidence_second
    by_cases ha : M.atom (r.edge t.second).val = v <;>
      by_cases hb : M.atom (M.mate (r.edge t.second).val) = v
    all_goals simp_all [appbIncidence]
  other := by
    intro i hi hj
    have hh := t.incidence_other i hi hj
    by_cases ha : M.atom (r.edge i).val = v <;> by_cases hb : M.atom (M.mate (r.edge i).val) = v
    all_goals simp_all [appbIncidence]

end AppbLocalPair

theorem appb_cutSign_singleton (M : Molecule V D) (v : V) (x : D) :
    appbCutSign M {v} x = appbIncidenceSign M v x := by
  simp only [appbCutSign,appbIncidenceSign,mem_singleton]

end WaveTurbulence.Mole
