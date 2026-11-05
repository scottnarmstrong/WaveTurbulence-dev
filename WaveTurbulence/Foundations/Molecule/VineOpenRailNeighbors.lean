/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCapBonds
public import WaveTurbulence.Foundations.Molecule.VineFreshRailNeighbors
import Mathlib.Tactic

/-! # Exact neighbor rows on a rail stopped at its last selected atom -/

public section
namespace WaveTurbulence.Vine

/-- Adding the terminal edge closes an open rail. -/
theorem railBonds_eq_open (a b : ℕ) (ws : List ℕ) :
    railBonds a ws b=openRailBonds a ws++[(ws.getLastD a,b)] := by
  induction ws generalizing a with
  | nil => rfl
  | cons w ws ih =>
    rw [railBonds_cons,openRailBonds_cons,List.cons_append,List.getLastD_cons,ih]

/-- The last label of a nonempty allocation is its upper endpoint minus one. -/
theorem allocated_getLastD (N a k : ℕ) (hk : 1 ≤ k) :
    ((List.range k).map (N+·)).getLastD a=N+k-1 := by
  obtain ⟨j,rfl⟩ : ∃ j,k=j+1 := ⟨k-1,by omega⟩
  rw [List.range_succ,List.map_append,List.map_cons,List.map_nil,List.getLastD_concat]
  omega

/-- An open rail gives no neighbor at a label absent from all its vertices. -/
theorem openRail_neighbors_zero (a v : ℕ) (ws : List ℕ) (ha : a ≠ v)
    (hw : ∀ w ∈ ws,w ≠ v) : edgeListNeighbors (openRailBonds a ws) v=0 := by
  apply edgeListNeighbors_zero
  intro e he
  have hh := List.of_mem_zip he
  constructor
  · rcases List.mem_cons.mp hh.1 with he | he
    · exact he ▸ ha
    · exact hw _ he
  · exact hw _ hh.2

/-- An allocated open rail contributes its first fresh label at its old
start, or contributes nothing if it contains no selected fresh atom. -/
theorem openRail_start_neighbors (N a k : ℕ) (ha : a<N) :
    edgeListNeighbors (openRailBonds a ((List.range k).map (N+·))) a=
      if k=0 then 0 else {N} := by
  cases k with
  | zero => rfl
  | succ k =>
    rw [mapped_range_succ,openRailBonds_cons,edgeListNeighbors_cons]
    have hNa : N ≠ a := by omega
    have hz := openRail_neighbors_zero N a ((List.range k).map (N+1+·)) hNa (by
      intro w hw
      obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hw
      omega)
    simp only [hNa,ite_false,ite_true,hz,add_zero,Nat.add_eq_zero_iff,Nat.one_ne_zero,
      and_false]

/-- Every selected allocated atom has its predecessor and, except at the
terminal selected atom, its successor. No bond continues beyond the open rail. -/
theorem openRail_allocated_neighbors (N a b k i : ℕ) (ha : a<N) (hb : b<N) (hi : i<k) :
    edgeListNeighbors (openRailBonds a ((List.range k).map (N+·))) (N+i)=
      {if i=0 then a else N+i-1}+(if i+1<k then {N+i+1} else 0) := by
  have hh := congrArg (fun es => edgeListNeighbors es (N+i))
    (railBonds_eq_open a b ((List.range k).map (N+·)))
  rw [edgeListNeighbors_append,allocated_getLastD N a k (by omega),
    rail_allocated_neighbors N a b k i ha hb hi] at hh
  have hbn : b ≠ N+i := by omega
  by_cases hnext : i+1<k
  · have hlast : N+k-1 ≠ N+i := by omega
    have hz : edgeListNeighbors [(N+k-1,b)] (N+i)=0 := by
      simp only [edgeListNeighbors_cons,hlast,hbn,ite_false,zero_add]
      rfl
    rw [hz,add_zero] at hh
    simpa only [hnext,ite_true] using hh.symm
  · have hlast : N+k-1=N+i := by omega
    have hz : edgeListNeighbors [(N+k-1,b)] (N+i)={b} := by
      simp only [edgeListNeighbors_cons,hlast,hbn,ite_false,ite_true,add_zero]
      rfl
    rw [hz] at hh
    simp only [hnext,ite_false] at hh ⊢
    rw [add_zero]
    exact add_right_cancel hh.symm

end WaveTurbulence.Vine
