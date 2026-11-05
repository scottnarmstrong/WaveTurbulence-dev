/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSideRailLists
public import WaveTurbulence.Foundations.Molecule.VineRungNeighbors
import Mathlib.Tactic

/-! # Exact rail and rung multiset decompositions for the side graph -/

public section
namespace WaveTurbulence.Vine

/-- A raw first edge gives one singleton multiset summand. -/
theorem rawBondMultiset_cons (e : ℕ×ℕ) (es : List (ℕ×ℕ)) :
    rawBondMultiset (e::es)={s(e.1,e.2)}+rawBondMultiset es := rfl

/-- The singleton raw list retains its one undirected bond. -/
theorem rawBondMultiset_singleton (e : ℕ×ℕ) :
    rawBondMultiset [e]={s(e.1,e.2)} := rfl

/-- The first and last side rails surround a reversed middle rail. -/
theorem side_full_rail_bonds (a b N m : ℕ) :
    rawBondMultiset (railBonds a ((List.range (m+2)).map (N+·)) b)=
      {s(a,N)}+rawBondMultiset (railBonds (N+(m+1))
        ((List.range m).map (fun i => N+(m-i))) N)+{s(N+(m+1),b)} := by
  rw [side_full_rail_list,railBonds_cons,railBonds_snoc]
  rw [rawBondMultiset_cons,rawBondMultiset_append,rawBondMultiset_singleton,
    rawBondMultiset_rail_reverse]
  exact (add_assoc _ _ _).symm

/-- Duplicating every raw edge doubles the entire undirected multiset. -/
theorem rawBondMultiset_double (es : List (ℕ×ℕ)) :
    rawBondMultiset (es.flatMap (fun p => [p,p]))=
      rawBondMultiset es+rawBondMultiset es := by
  induction es with
  | nil => simp [rawBondMultiset]
  | cons e es ih =>
    simp only [List.flatMap_cons,rawBondMultiset_append,ih]
    simp only [rawBondMultiset_cons,show rawBondMultiset []=0 from rfl,add_zero]
    ac_rfl

/-- The allocated double rungs are twice the multiset of their paired labels. -/
theorem rawBondMultiset_allocated (N P k : ℕ) :
    rawBondMultiset (allocatedRungs N P k)=
      ((List.range k : Multiset ℕ).map (fun i => s(N+i,P+i)))+
      ((List.range k : Multiset ℕ).map (fun i => s(N+i,P+i))) := by
  have he : allocatedRungs N P k=
      ((List.range k).map (fun i => (N+i,P+i))).flatMap (fun p => [p,p]) := by
    simp only [allocatedRungs,List.flatMap_map]
  rw [he,rawBondMultiset_double]
  simp only [rawBondMultiset,Multiset.map_coe,List.map_map,Function.comp_def]

/-- Reversing the middle rung indices preserves their paired undirected
bond multiset; both rail labels use the same permutation. -/
theorem middle_rungs_reverse (N P m : ℕ) :
    ((List.range m : Multiset ℕ).map (fun i => s(N+(m-i),P+(m-i))))=
      ((List.range m : Multiset ℕ).map (fun i => s(N+1+i,P+1+i))) := by
  have he : (List.range' 1 m).reverse=(List.range m).map (fun i => m-i) := by
    simpa using (List.reverse_range' (s:=1) (n:=m))
  have hm := congrArg (fun l : List ℕ =>
    (l.map (fun i => s(N+i,P+i)) : Multiset (Sym2 ℕ))) he
  simpa [List.map_reverse,Multiset.coe_reverse,List.range'_eq_map_range,
    List.map_map,Function.comp_def,Nat.add_assoc] using hm.symm

/-- Full rung allocation decomposes into its first and last double rungs
and the same descending middle used by the canonical V template. -/
theorem side_full_rungs (N P m : ℕ) :
    rawBondMultiset (allocatedRungs N P (m+2))=
      ({s(N,P)}+{s(N+(m+1),P+(m+1))}+
        (List.range m : Multiset ℕ).map (fun i => s(N+(m-i),P+(m-i))))+
      ({s(N,P)}+{s(N+(m+1),P+(m+1))}+
        (List.range m : Multiset ℕ).map (fun i => s(N+(m-i),P+(m-i)))) := by
  rw [rawBondMultiset_allocated,middle_rungs_reverse]
  have he : (List.range (m+2) : Multiset ℕ).map (fun i => s(N+i,P+i))=
      {s(N,P)}+{s(N+(m+1),P+(m+1))}+
        (List.range m : Multiset ℕ).map (fun i => s(N+1+i,P+1+i)) := by
    rw [show m+2=(m+1)+1 by omega,List.range_succ,List.range_succ_eq_map]
    simp [Multiset.map_coe,List.map_append,List.map_map,Function.comp_def,
      add_comm,add_left_comm]
  rw [he]

end WaveTurbulence.Vine
