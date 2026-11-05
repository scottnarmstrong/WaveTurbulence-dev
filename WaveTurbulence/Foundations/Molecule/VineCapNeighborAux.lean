/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineOpenRailNeighbors
public import WaveTurbulence.Foundations.Molecule.VineCapIndices
import Mathlib.Tactic

/-! # Local numeric and support facts for literal cap neighbor rows -/

public section
namespace WaveTurbulence.Vine

/-- The normal triangle center has its two doubled leg neighbors. -/
theorem capTriangle_neighbors_center : edgeListNeighbors capTriangleBonds 4={5}+{5}+{6}+{6} := by decide

/-- The upper triangle leg has two center incidences and its single other leg. -/
theorem capTriangle_neighbors_upper : edgeListNeighbors capTriangleBonds 5={4}+{4}+{6} := by decide

/-- The lower triangle leg has the symmetric triangle row. -/
theorem capTriangle_neighbors_lower : edgeListNeighbors capTriangleBonds 6={4}+{4}+{5} := by decide

/-- No fresh cap atom is an endpoint of a triangle bond. -/
theorem capTriangle_neighbors_fresh (v : ℕ) (hv : 9 ≤ v) :
    edgeListNeighbors capTriangleBonds v=0 := by
  apply edgeListNeighbors_zero
  intro e he
  simp only [capTriangleBonds,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl <;> constructor <;> omega

/-- An allocated open rail has no incidence outside its allocation and start. -/
theorem openRail_allocated_neighbors_zero (N a k v : ℕ) (ha : a ≠ v)
    (hv : v<N ∨ N+k ≤ v) :
    edgeListNeighbors (openRailBonds a ((List.range k).map (N+·))) v=0 := by
  apply openRail_neighbors_zero a v _
  · exact ha
  · intro w hw
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
    have := List.mem_range.mp hi
    omega

/-- Double rung allocations have no incidence before either allocated rail. -/
theorem allocatedRungs_neighbors_zero_before (N P k v : ℕ) (hN : v<N) (hP : v<P) :
    edgeListNeighbors (allocatedRungs N P k) v=0 := by
  apply edgeListNeighbors_zero
  intro e he
  obtain ⟨i,_hi,rfl⟩ := allocatedRungs_mem he
  constructor <;> omega

end WaveTurbulence.Vine
