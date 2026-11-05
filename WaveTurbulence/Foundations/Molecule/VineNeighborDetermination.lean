/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineNeighborMultiset
import Mathlib.Tactic

/-! # Complete neighbor rows determine an undirected bond multiset -/

public section
namespace WaveTurbulence.Vine

/-- A neighbor count recovers one edge multiplicity, with factor two only
on a diagonal loop. The ambient label space may be infinite. -/
theorem bondNeighbors_count (e : Sym2 ℕ) (u v : ℕ) :
    (bondNeighbors e u).count v=
      if e=s(u,v) then (if u=v then 2 else 1) else 0 := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    by_cases ha : a=u <;> by_cases hb : b=u <;>
      by_cases hav : a=v <;> by_cases hbv : b=v <;> by_cases huv : u=v <;>
      simp_all [bondNeighbors_pair,eq_comm]

/-- The complete edge multiset's neighbor counts recover its multiplicities. -/
theorem neighborSum_count (E : Multiset (Sym2 ℕ)) (u v : ℕ) :
    ((E.map (fun e => bondNeighbors e u)).sum).count v=
      (if u=v then 2 else 1)*E.count s(u,v) := by
  induction E using Multiset.induction_on with
  | empty => simp
  | @cons e E ih =>
    simp only [Multiset.map_cons,Multiset.sum_cons,Multiset.count_add,ih,bondNeighbors_count]
    by_cases he : e=s(u,v) <;> by_cases huv : u=v <;>
      simp_all [Nat.mul_add,eq_comm,Nat.add_comm]

/-- Equality of complete neighbor rows determines every undirected bond,
including loops and all parallel multiplicities. -/
theorem bondMultiset_eq_of_neighbors {E F : Multiset (Sym2 ℕ)}
    (h : ∀ u,(E.map (fun e => bondNeighbors e u)).sum=
      (F.map (fun e => bondNeighbors e u)).sum) : E=F := by
  apply Multiset.ext.mpr
  intro e
  induction e using Sym2.inductionOn with
  | _ u v =>
    have hh := congrArg (Multiset.count v) (h u)
    rw [neighborSum_count,neighborSum_count] at hh
    split_ifs at hh <;> omega

end WaveTurbulence.Vine
