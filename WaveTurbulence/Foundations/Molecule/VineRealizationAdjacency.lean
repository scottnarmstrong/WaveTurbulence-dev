/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRealizationInverse
public import WaveTurbulence.Foundations.Molecule.VineGroupAdjacency
public import WaveTurbulence.Foundations.Molecule.VinePaths
public import WaveTurbulence.Foundations.Molecule.MoleculeBlockBarriers
import Mathlib.Tactic

/-! # Lift literal template edges into arbitrary actual subgroups -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Every literal template edge lifts to an actual induced edge between
its uniquely labeled atoms. -/
theorem VineRealization.adj_of_edge {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    {u v : V} (hu : u ∈ S) (hv : v ∈ S)
    (hedge : EdgeAdj (X.expand R.k).bonds (R.f u) (R.f v)) : M.Adj u v := by
  have hm : s(R.f u,R.f v) ∈
      ((X.expand R.k).bonds.map (fun e => s(e.1,e.2)) : Multiset (Sym2 ℕ)) := by
    rcases hedge with he | he
    · exact Multiset.mem_coe.mpr (List.mem_map.mpr ⟨_,he,rfl⟩)
    · exact Multiset.mem_coe.mpr (List.mem_map.mpr ⟨_,he,Sym2.eq_swap⟩)
  rw [← R.bonds_eq] at hm
  simp only [Molecule.groupBonds,Multiset.map_map,Multiset.mem_map,
    Finset.mem_val,mem_filter,mem_univ,true_and,Function.comp_apply] at hm
  obtain ⟨x,⟨_hx,hg⟩,hx⟩ := hm
  have heq := Sym2.eq_iff.mp hx
  change (R.f (M.atom x)=R.f u ∧ R.f (M.atom (M.mate x))=R.f v) ∨
    (R.f (M.atom x)=R.f v ∧ R.f (M.atom (M.mate x))=R.f u) at heq
  rcases heq with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact ⟨x,R.injOn hg.1 hu h1,R.injOn hg.2 hv h2⟩
  · exact ⟨M.mate x,R.injOn hg.2 hu h2,by rw [M.mate_mate]; exact R.injOn hg.1 hv h1⟩

/-- A literal edge between two selected atoms is present in their actual
induced subgroup. -/
theorem VineRealization.subgroup_adj_of_edge {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    {A : Finset V} (hAS : A ⊆ S) {u v : V} (hu : u ∈ A) (hv : v ∈ A)
    (hedge : EdgeAdj (X.expand R.k).bonds (R.f u) (R.f v)) :
    (Mole.induced M A).Adj u v :=
  (Mole.induced_adj_iff M A u v).mpr ⟨R.adj_of_edge (hAS hu) (hAS hv) hedge,hu,hv⟩

end WaveTurbulence.Vine
