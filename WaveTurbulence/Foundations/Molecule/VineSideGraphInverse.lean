/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSideGraph
public import WaveTurbulence.Foundations.Molecule.VineExpansionEndpoints
import Mathlib.Tactic

/-! # The inverse explicit side relabeling transports the exact bonds -/

public section
namespace WaveTurbulence.Vine

/-- Relabel the side bonds back to the literal expanded V bonds. -/
theorem sideInverse_bonds (N m : ℕ) (hN : 9 ≤ N) :
    (rawBondMultiset (sideBonds N (m+2))).map (Sym2.map (sideInverse N m))=
      rawBondMultiset (VineType.V.expand [m]).bonds := by
  rw [← sideEmbedding_bonds,Multiset.map_map]
  calc
    _ = (rawBondMultiset (VineType.V.expand [m]).bonds).map id := by
      apply Multiset.map_congr rfl
      intro e he
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp he)
      have hb := expand_endpoints .V [m] p hp
      have hn : (VineType.V.expand [m]).n=9+2*m := by
        rw [expand_atoms]
        rfl
      rw [hn] at hb
      simp only [Function.comp_def,Sym2.map_mk,
        sideInverse_sideEmbedding N m p.1 hN hb.1,
        sideInverse_sideEmbedding N m p.2 hN hb.2,id_eq]
    _ = _ := Multiset.map_id _

end WaveTurbulence.Vine
