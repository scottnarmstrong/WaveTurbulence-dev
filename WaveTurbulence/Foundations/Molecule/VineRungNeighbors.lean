/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRailNeighbors
import Mathlib.Tactic

/-! # Literal neighbor rows of doubled allocated rungs -/

public section
namespace WaveTurbulence.Vine

/-- The doubled rung list at consecutive allocated names. -/
@[expose] def allocatedRungs (n m k : ℕ) : List (ℕ × ℕ) :=
  (List.range k).flatMap (fun i => [(n+i,m+i),(n+i,m+i)])

/-- Splitting the first rung shifts both allocated intervals by one. -/
theorem allocatedRungs_succ (n m k : ℕ) :
    allocatedRungs n m (k+1)=(n,m)::(n,m)::allocatedRungs (n+1) (m+1) k := by
  simp only [allocatedRungs,List.range_succ_eq_map,List.flatMap_cons,
    List.flatMap_map,Nat.add_zero,List.cons_append,List.nil_append]
  congr 2
  apply List.flatMap_congr
  intro i _hi
  have hn : n+(i+1)=n+1+i := by omega
  have hm : m+(i+1)=m+1+i := by omega
  simp only [hn,hm]

/-- Every endpoint of a doubled rung belongs to one of the allocated intervals. -/
theorem allocatedRungs_mem {n m k : ℕ} {e : ℕ × ℕ} (he : e ∈ allocatedRungs n m k) :
    ∃ i < k, e=(n+i,m+i) := by
  obtain ⟨i,hi,he⟩ := List.mem_flatMap.mp he
  refine ⟨i,List.mem_range.mp hi,?_⟩
  simpa using he

/-- A fresh left-rail atom has exactly two copies of its right-rail partner
among the doubled rung bonds. -/
theorem allocatedRungs_neighbors_left (n m k i : ℕ) (hsep : n+k ≤ m) (hi : i < k) :
    edgeListNeighbors (allocatedRungs n m k) (n+i)={m+i}+{m+i} := by
  induction k generalizing n m i with
  | zero => omega
  | succ k ih =>
    rw [allocatedRungs_succ]
    cases i with
    | zero =>
      have hmn : m ≠ n := by omega
      have hz : edgeListNeighbors (allocatedRungs (n+1) (m+1) k) n=0 := by
        apply edgeListNeighbors_zero
        intro e he
        obtain ⟨j,_hj,rfl⟩ := allocatedRungs_mem he
        constructor <;> omega
      simp only [edgeListNeighbors_cons,hmn,ite_false,ite_true,hz,
        add_zero]
    | succ i =>
      have hr := ih (n+1) (m+1) i (by omega) (by omega)
      have hn : n ≠ n+1+i := by omega
      have hm : m ≠ n+1+i := by omega
      have hp : n+(i+1)=n+1+i := by omega
      have hq : m+(i+1)=m+1+i := by omega
      simp only [edgeListNeighbors_cons,hp,hq,hn,hm,ite_false,zero_add]
      exact hr

/-- A fresh right-rail atom has the two copies of its left-rail partner. -/
theorem allocatedRungs_neighbors_right (n m k i : ℕ) (hsep : n+k ≤ m) (hi : i < k) :
    edgeListNeighbors (allocatedRungs n m k) (m+i)={n+i}+{n+i} := by
  induction k generalizing n m i with
  | zero => omega
  | succ k ih =>
    rw [allocatedRungs_succ]
    cases i with
    | zero =>
      have hnm : n ≠ m := by omega
      have hz : edgeListNeighbors (allocatedRungs (n+1) (m+1) k) m=0 := by
        apply edgeListNeighbors_zero
        intro e he
        obtain ⟨j,hj,rfl⟩ := allocatedRungs_mem he
        constructor <;> omega
      simp only [edgeListNeighbors_cons,hnm,ite_false,ite_true,hz,zero_add,add_zero]
    | succ i =>
      have hr := ih (n+1) (m+1) i (by omega) (by omega)
      have hn : n ≠ m+1+i := by omega
      have hm : m ≠ m+1+i := by omega
      have hp : m+(i+1)=m+1+i := by omega
      have hq : n+(i+1)=n+1+i := by omega
      simp only [edgeListNeighbors_cons,hp,hq,hn,hm,ite_false,zero_add]
      exact hr

/-- The allocated-rung list is the literal zip/flatMap in the pinned insertion. -/
theorem allocatedRungs_eq_zip (n m k : ℕ) :
    allocatedRungs n m k=
      (List.zip ((List.range k).map (n+·)) ((List.range k).map (m+·))).flatMap
        (fun p => [p,p]) := by
  rw [List.zip_map',List.flatMap_map]
  rfl

end WaveTurbulence.Vine
