/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCapActualNeighborRows
public import WaveTurbulence.Foundations.Molecule.VineCapBondSupport
public import WaveTurbulence.Foundations.Molecule.VineSupportedNeighbors
import Mathlib.Tactic

/-! # Primitive actual cap incidences reconstruct the entire exact bond multiset -/

public section
namespace WaveTurbulence.Vine

/-- The raw-list and undirected-multiset neighbor conventions agree. -/
theorem rawBondMultiset_neighborSum (es : List (ℕ×ℕ)) (u : ℕ) :
    ((rawBondMultiset es).map (fun e => bondNeighbors e u)).sum=edgeListNeighbors es u := by
  simp only [rawBondMultiset,Multiset.map_coe,Multiset.sum_coe,List.map_map,
    Function.comp_def,edgeListNeighbors]

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace CapPrefixData
variable {M : Molecule V D} {A : Finset V} {n r : ℕ} (C : CapPrefixData M A n r)

/-- Every selected primitive cap atom and actual dart row reconstructs
exactly the full literal cap graph. No graph-isomorphism premise is assumed:
finite atom labels, all neighbor rows, and both endpoint supports are proved. -/
theorem bonds_eq (hM : M.IsMolecule) :
    (M.groupBonds A).map (Sym2.map C.label)=rawBondMultiset (capBonds 9 r) := by
  apply bondMultiset_eq_of_supported_neighbors (capLabels 9 r)
  · intro e he a ha
    have hh := mapped_groupBonds_support M A C.label e he a ha
    rwa [C.label_image] at hh
  · exact capBondMultiset_support 9 r
  · intro u hu
    have hi : u ∈ (Finset.univ : Finset (CapIndex r)).image (capIndexLabel 9 r) := by
      rwa [capIndexLabel_image]
    obtain ⟨i,_hi,rfl⟩ := Finset.mem_image.mp hi
    have hactual := mappedGroupNeighbors_eq_bonds M (Finset.Subset.refl A)
      C.label C.label_injOn (C.family_mem i)
    rw [C.label_family] at hactual
    calc
      _ = mappedGroupNeighbors M A C.label (C.family i) := hactual.symm
      _ = capNeighborRow r i := C.mapped_neighbor_row hM i
      _ = _ := by rw [rawBondMultiset_neighborSum,capBonds_neighbor_row]

end CapPrefixData
end WaveTurbulence.Vine
