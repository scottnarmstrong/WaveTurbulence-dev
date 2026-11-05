/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineBondRestriction
public import WaveTurbulence.Foundations.Molecule.VineRealizationGroups
import Mathlib.Tactic

/-! # Exact internal degrees of nested groups in a vine realization -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- The pinned realization restricts to any actual atomic subgroup by
filtering the literal expanded edge list at the image atom set. -/
theorem VineRealization.subgroup_bonds {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    {A : Finset V} (hAS : A ⊆ S) :
    (M.groupBonds A).map (Sym2.map R.f)=
      (((X.expand R.k).bonds.filter (fun e => e.1 ∈ A.image R.f ∧ e.2 ∈ A.image R.f)).map
        (fun e => s(e.1,e.2)) : Multiset (Sym2 ℕ)) := by
  rw [mapped_groupBonds_filter M hAS R.f R.injOn,R.bonds_eq]
  simp only [Multiset.filter_coe,List.filter_map,Function.comp_def,mk_mem_sym2_iff]

/-- Degrees of actual nested groups equal literal induced-template degrees.
This applies to every subgroup, not only vine-like ones. -/
theorem VineRealization.subgroup_degree {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    {A : Finset V} (hAS : A ⊆ S) {v : V} (hv : v ∈ S) :
    M.degIn A v=edgeDegree
      ((X.expand R.k).bonds.filter (fun e => e.1 ∈ A.image R.f ∧ e.2 ∈ A.image R.f)) (R.f v) := by
  rw [degreeIn_eq_mapped_bondIncidence M hAS R.f R.injOn hv,R.subgroup_bonds hAS]
  exact edgeList_incidence_degree _ _

/-- Zero additional rungs means exactly the pinned base template. -/
theorem expand_zero_rungs (X : VineType) :
    X.expand (List.replicate X.template.slots.length 0)=X.template := by
  cases X <;> rfl

end WaveTurbulence.Vine
