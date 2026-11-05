/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSideBonds
public import WaveTurbulence.Foundations.Molecule.VineRailReversal
import Mathlib.Tactic

/-! # Uniform raw-edge normal form of the pinned type-V expansion -/

public section
namespace WaveTurbulence.Vine

/-- The fourteen type-V edges outside its unique replaceable slot. -/
@[expose] def typeVFixedBonds : List (ℕ×ℕ) :=
  [(0,1),(0,2),(1,3),(2,3),(2,3),(4,5),(4,5),(4,6),(5,7),
    (6,7),(6,8),(6,8),(7,8),(7,8)]

/-- The pinned expansion has this same formula even with zero extra rungs:
the two rails then supply exactly the two original slot bonds. -/
theorem typeV_expand_bonds (m : ℕ) : (VineType.V.expand [m]).bonds=
    typeVFixedBonds++railBonds 2 ((List.range m).map (9+·)) 4++
      railBonds 3 ((List.range m).map (9+m+·)) 5++allocatedRungs 9 (9+m) m := by
  by_cases hm : m=0
  · subst m
    rfl
  · simp only [VineType.expand,VineType.template,List.zip_cons_cons,List.zip_nil_left,
      List.foldl_cons,List.foldl_nil,insertRungs,hm,ite_false]
    rw [← allocatedRungs_eq_zip]
    rfl

/-- Relabeling raw endpoints commutes with forgetting edge directions. -/
theorem rawBondMultiset_map (f : ℕ → ℕ) (es : List (ℕ×ℕ)) :
    rawBondMultiset (es.map (fun p => (f p.1,f p.2)))=
      (rawBondMultiset es).map (Sym2.map f) := by
  simp only [rawBondMultiset,Multiset.map_coe,List.map_map]
  rfl

end WaveTurbulence.Vine
