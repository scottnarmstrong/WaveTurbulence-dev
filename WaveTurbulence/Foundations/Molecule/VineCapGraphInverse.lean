/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCapSideGraph
public import WaveTurbulence.Foundations.Molecule.VineCapBijection
public import WaveTurbulence.Foundations.Molecule.VineSideEndpointMembership
import Mathlib.Tactic

/-! # Recovering the side graph after deleting the cap's extra joint bond -/

public section
namespace WaveTurbulence.Vine

/-- The inverse relabeling recovers the raw side edge list exactly. -/
theorem capToSide_bonds (N k : ℕ) (hN : 9 ≤ N) :
    (capAdjointBonds N k).map (fun p => (capToSide N k p.1,capToSide N k p.2))=
      sideBonds N k := by
  rw [← sideToCap_bonds N k hN,List.map_map]
  calc
    _ = (sideBonds N k).map id := by
      apply List.map_congr_left
      intro p hp
      have hh := sideBonds_endpoints_mem N k p hp
      simp only [Function.comp_def,capToSide_sideToCap N k p.1 hN hh.1,
        capToSide_sideToCap N k p.2 hN hh.2,id_eq]
    _ = _ := List.map_id _

/-- The inverse relabeling recovers the undirected side multiset exactly. -/
theorem capToSide_bondMultiset (N k : ℕ) (hN : 9 ≤ N) :
    (rawBondMultiset (capAdjointBonds N k)).map (Sym2.map (capToSide N k))=
      rawBondMultiset (sideBonds N k) := by
  rw [← rawBondMultiset_map,capToSide_bonds N k hN]

/-- The terminal cap upper joint maps to old side joint7. -/
theorem capToSide_upper_joint (N k : ℕ) : capToSide N k (N+k)=7 := by
  simp only [capToSide,ite_true]

/-- The terminal cap lower joint maps to old side joint8. -/
theorem capToSide_lower_joint (N k : ℕ) : capToSide N k (N+(k+1)+k)=8 := by
  have he : N+(k+1)+k ≠ N+k := by omega
  simp only [capToSide,he,ite_false,ite_true]

end WaveTurbulence.Vine
