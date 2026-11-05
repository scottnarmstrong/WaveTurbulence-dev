/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRailNeighbors
import Mathlib.Tactic

/-! # Exact neighbor row at every freshly allocated rail vertex -/

public section
namespace WaveTurbulence.Vine

/-- At the i-th allocated rail atom, the neighbors are its predecessor and
successor, with a and b supplying the boundary positions. -/
theorem rail_allocated_neighbors (n a b k i : ℕ) (ha : a<n) (hb : b<n) (hi : i<k) :
    edgeListNeighbors (railBonds a ((List.range k).map (n+·)) b) (n+i)=
      {if i=0 then a else n+i-1}+{if i+1<k then n+i+1 else b} := by
  induction k generalizing n a b i with
  | zero => omega
  | succ k ih =>
    rw [mapped_range_succ]
    change edgeListNeighbors ((a,n)::railBonds n ((List.range k).map (n+1+·)) b) (n+i)= _
    cases i with
    | zero =>
      have han : a ≠ n := by omega
      have hbn : b ≠ n := by omega
      have hrest := rail_start_neighbors n b ((List.range k).map (n+1+·)) hbn (by
        intro w hw
        obtain ⟨j,_hj,rfl⟩ := List.mem_map.mp hw
        omega)
      have hhead : ((List.range k).map (n+1+·)).headD b=
          if 1<k+1 then n+1 else b := by
        cases k with
        | zero => rfl
        | succ k =>
          rw [mapped_range_succ]
          have hpos : 1<k+1+1 := by omega
          simp only [List.headD_cons,hpos,ite_true]
      simp only [Nat.add_zero,edgeListNeighbors_cons,han,ite_false,ite_true,zero_add,hrest,hhead]
    | succ i =>
      have hrec := ih (n+1) n b i (by omega) (by omega) (by omega)
      have hprev : (if i=0 then n else n+1+i-1)=
          if i+1=0 then a else n+(i+1)-1 := by
        by_cases h : i=0 <;> simp [h,Nat.add_left_comm,Nat.add_comm]
      have hnext : (if i+1<k then n+1+i+1 else b)=
          if (i+1)+1<k+1 then n+(i+1)+1 else b := by split_ifs <;> omega
      rw [hprev,hnext] at hrec
      have han : a ≠ n+1+i := by omega
      have hnn : n ≠ n+1+i := by omega
      have hpoint : n+(i+1)=n+1+i := by omega
      simpa only [edgeListNeighbors_cons,hpoint,han,hnn,ite_false,zero_add] using hrec

end WaveTurbulence.Vine
