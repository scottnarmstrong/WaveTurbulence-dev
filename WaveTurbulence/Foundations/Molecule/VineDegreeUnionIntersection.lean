/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeGroups
import Mathlib.Tactic

/-! # Exact degree inclusion-exclusion at a shared atom -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- At an atom common to two groups, internal dart sets obey exact
union/intersection inclusion-exclusion. Parallel bonds and loops are retained. -/
theorem degIn_union_inter (M : Molecule V D) (S T : Finset V) (v : V)
    (hvS : v ∈ S) (hvT : v ∈ T) :
    M.degIn (S ∪ T) v+M.degIn (S ∩ T) v=M.degIn S v+M.degIn T v := by
  classical
  let F := fun A => (M.dartsAt v).filter (M.InGroup A)
  have hU : F S ∪ F T=F (S ∪ T) := by
    ext d
    by_cases hd : M.atom d=v
    · simp only [F,Molecule.dartsAt,mem_filter,mem_univ,true_and,Molecule.InGroup,mem_union,hd,
        hvS,hvT,true_and,true_or]
    · simp only [F,Molecule.dartsAt,mem_filter,mem_univ,true_and,hd,false_and,mem_union,false_or]
  have hI : F S ∩ F T=F (S ∩ T) := by
    ext d
    simp only [F,mem_inter,mem_filter,Molecule.InGroup]
    tauto
  have hh := card_union_add_card_inter (F S) (F T)
  rw [hU,hI] at hh
  exact hh

end WaveTurbulence.Vine
