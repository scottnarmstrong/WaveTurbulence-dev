/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSelectedAtoms
public import WaveTurbulence.Foundations.Molecule.VineBondRestriction
public import WaveTurbulence.Foundations.Molecule.VineRestrictBonds
public import WaveTurbulence.Foundations.Molecule.VineRailReversal
import Mathlib.Tactic

/-! # Exact bonds of a label-selected actual subgroup -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Restricting the raw edge list is the induced undirected bond filter. -/
theorem rawBondMultiset_restrict (W : Finset ℕ) (es : List (ℕ×ℕ)) :
    rawBondMultiset (restrictBonds W es)=
      (rawBondMultiset es).filter (fun e => e ∈ W.sym2) := by
  simp only [rawBondMultiset,restrictBonds,Multiset.filter_coe,List.filter_map,
    Function.comp_def,mk_mem_sym2_iff]

/-- An available label selection has exactly the induced raw-template bonds,
without any presumption that the selected group is itself a vine. -/
theorem VineRealization.selected_bonds {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b) (W : Finset ℕ)
    (hW : W ⊆ range (X.expand R.k).n) :
    (M.groupBonds (R.selectedAtoms W)).map (Sym2.map R.f)=
      rawBondMultiset (restrictBonds W (X.expand R.k).bonds) := by
  have hsub : R.selectedAtoms W ⊆ S := fun _ h => (mem_filter.mp h).1
  rw [mapped_groupBonds_filter M hsub R.f R.injOn,R.bonds_eq,
    R.image_selectedAtoms,inter_eq_left.mpr hW,rawBondMultiset_restrict]
  rfl

end WaveTurbulence.Vine
