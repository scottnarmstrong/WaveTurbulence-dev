/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSideRailBonds
public import WaveTurbulence.Foundations.Molecule.VineTypeVEdges
import Mathlib.Tactic

/-! # The full VII side is exactly an expanded type-V undirected graph -/

public section
namespace WaveTurbulence.Vine

/-- The canonical middle double rungs map to the descending full-side middle. -/
theorem sideEmbedding_rungs (N m : ℕ) :
    (rawBondMultiset (allocatedRungs 9 (9+m) m)).map (Sym2.map (sideEmbedding N m))=
      ((List.range m : Multiset ℕ).map
        (fun i => s(N+(m-i),N+(m+2)+(m-i))))+
      ((List.range m : Multiset ℕ).map
        (fun i => s(N+(m-i),N+(m+2)+(m-i)))) := by
  rw [rawBondMultiset_allocated,Multiset.map_add]
  have he : ((List.range m : Multiset ℕ).map (fun i => s(9+i,9+m+i))).map
      (Sym2.map (sideEmbedding N m))=
      (List.range m : Multiset ℕ).map (fun i => s(N+(m-i),N+(m+2)+(m-i))) := by
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro i hi
    have him : i < m := List.mem_range.mp (Multiset.mem_coe.mp hi)
    simp only [Function.comp_def,Sym2.map_mk,sideEmbedding_upper N m i him,
      sideEmbedding_lower]
  rw [he]

/-- Literal type-V and side bond multisets agree after the explicit relabeling.
The side has m+2 full rungs, while the pinned V expansion inserts m extra rungs. -/
theorem sideEmbedding_bonds (N m : ℕ) :
    (rawBondMultiset (VineType.V.expand [m]).bonds).map (Sym2.map (sideEmbedding N m))=
      rawBondMultiset (sideBonds N (m+2)) := by
  rw [typeV_expand_bonds]
  simp only [rawBondMultiset_append,Multiset.map_add]
  rw [← rawBondMultiset_map (sideEmbedding N m) typeVFixedBonds,
    ← rawBondMultiset_map (sideEmbedding N m) (railBonds 2 _ 4),
    ← rawBondMultiset_map (sideEmbedding N m) (railBonds 3 _ 5),
    railBonds_map,railBonds_map,sideEmbedding_upper_list,sideEmbedding_lower_list,
    sideEmbedding_rungs]
  simp only [sideEmbedding]
  rw [sideBonds]
  simp only [rawBondMultiset_append]
  rw [side_full_rail_bonds,side_full_rail_bonds,side_full_rungs]
  simp only [typeVFixedBonds,List.map_cons,List.map_nil,rawBondMultiset_cons,
    show rawBondMultiset []=0 from rfl,add_zero]
  simp only [Sym2.eq_swap (a:=7) (b:=N+(m+1)),
    Sym2.eq_swap (a:=8) (b:=N+(m+2)+(m+1)),
    Sym2.eq_swap (a:=N) (b:=5),
    Sym2.eq_swap (a:=N+(m+2)) (b:=6),
    Sym2.eq_swap (a:=5) (b:=4),Sym2.eq_swap (a:=6) (b:=4)]
  simp only [Nat.add_assoc]
  ac_rfl

end WaveTurbulence.Vine
