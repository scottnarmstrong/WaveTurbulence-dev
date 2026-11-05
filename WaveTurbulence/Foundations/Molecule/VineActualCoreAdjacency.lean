/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRealizationAdjacency
public import WaveTurbulence.Foundations.Molecule.VineOldBondCounts
import Mathlib.Tactic

/-! # Actual old-core adjacency is already present in the pinned core -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Actual induced adjacency gives the corresponding undirected literal edge. -/
theorem VineRealization.edge_of_adj {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b u v : V} (R : VineRealization M X S a b)
    (hu : u ∈ S) (hv : v ∈ S) (ha : M.Adj u v) :
    EdgeAdj (X.expand R.k).bonds (R.f u) (R.f v) := by
  have hm := (mem_groupBonds_iff M S u v).mpr ⟨ha,hu,hv⟩
  have hh := Multiset.mem_map_of_mem (Sym2.map R.f) hm
  rw [R.bonds_eq] at hh
  obtain ⟨e,he,hh⟩ := List.mem_map.mp (Multiset.mem_coe.mp hh)
  rcases e with ⟨i,j⟩
  have heq := Sym2.eq_iff.mp hh
  change (i=R.f u ∧ j=R.f v) ∨ (i=R.f v ∧ j=R.f u) at heq
  rcases heq with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Or.inl (by simpa only [h1,h2] using he)
  · exact Or.inr (by simpa only [h1,h2] using he)

/-- No insertion can create a new edge between old core labels. -/
theorem VineRealization.old_edge_of_adj {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b u v : V} (R : VineRealization M X S a b)
    (hu : u ∈ S) (hv : v ∈ S) (huold : R.f u<X.template.n)
    (hvold : R.f v<X.template.n) (ha : M.Adj u v) :
    EdgeAdj X.template.bonds (R.f u) (R.f v) := by
  rcases R.edge_of_adj hu hv ha with he | he
  · exact Or.inl (List.count_pos_iff.mp ((List.count_pos_iff.mpr he).trans_le
      (expand_old_count_le X R.k _ _ huold hvold)))
  · exact Or.inr (List.count_pos_iff.mp ((List.count_pos_iff.mpr he).trans_le
      (expand_old_count_le X R.k _ _ hvold huold)))

end WaveTurbulence.Vine
