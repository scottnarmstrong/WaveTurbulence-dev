/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulence.Foundations.Molecule.VineActualPartition
public import WaveTurbulence.Foundations.Molecule.VineRealizationInverse
public import WaveTurbulence.Foundations.Molecule.MoleculeGroups
import Mathlib.Tactic

/-! # Source directed degree equations in arbitrary actual vine realizations -/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Internal outgoing degree never exceeds the ambient outgoing degree. -/
theorem outIn_le_outdeg (M : Molecule V D) (S : Finset V) (v : V) : M.outIn S v ≤ M.outdeg v := by
  apply card_le_card
  intro e he
  exact mem_filter.mpr ⟨(mem_filter.mp he).1,(mem_filter.mp he).2.2⟩

/-- The analogous bound for incoming darts. -/
theorem inIn_le_indeg (M : Molecule V D) (S : Finset V) (v : V) : M.inIn S v ≤ M.indeg v := by
  apply card_le_card
  intro e he
  exact mem_filter.mpr ⟨(mem_filter.mp he).1,(mem_filter.mp he).2.2⟩

/-- A block's nonjoints have exactly two internal darts of each direction. -/
theorem block_interior_directed_degrees (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b v : V} (hB : M.IsBlock S a b) (hv : v ∈ S)
    (hva : v ≠ a) (hvb : v ≠ b) : M.outIn S v=2 ∧ M.inIn S v=2 := by
  have hd := hB.2.2.2.2.2.2.2.2.1 v hv hva hvb
  have hout := outIn_le_outdeg M S v
  have hin := inIn_le_indeg M S v
  have hb := hM.1 v (hB.1 hv)
  have hs := Mole.outIn_add_inIn M S v
  omega

/-- The actual realization satisfies exactly the degree equations used by
the complete finite orientation classification. No direction is added to
or assumed from the pinned undirected template. -/
theorem realization_directed_degrees (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (hB : M.IsBlock S a b) (i : Fin (X.expand R.k).n) :
    M.outIn S (R.atomAt i).1=(if i.1<2 then 1 else 2) ∧
    M.inIn S (R.atomAt i).1=(if i.1<2 then 1 else 2) := by
  have hm := (R.atomAt i).2
  have hlabel := R.label_atomAt i
  have hj := realization_index_lt_two_iff R hB hm
  by_cases hi : i.1<2
  · have hj' : (R.atomAt i).1=a ∨ (R.atomAt i).1=b := hj.mp (hlabel.symm ▸ hi)
    rcases hj' with ha | hb
    · simpa only [ha,hi,ite_true] using And.intro hB.2.2.2.2.1 hB.2.2.2.2.2.1
    · simpa only [hb,hi,ite_true] using And.intro hB.2.2.2.2.2.2.1 hB.2.2.2.2.2.2.2.1
  · have hn : (R.atomAt i).1 ≠ a ∧ (R.atomAt i).1 ≠ b := by
      apply not_or.mp
      intro he
      have hh := hj.mpr he
      rw [hlabel] at hh
      exact hi hh
    simpa only [hi,ite_false] using block_interior_directed_degrees M hM hB hm hn.1 hn.2

end WaveTurbulence.Vine.Param
