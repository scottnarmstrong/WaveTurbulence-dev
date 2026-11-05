/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineShortSidePaths
public import WaveTurbulence.Foundations.Molecule.VineShortCapPaths
public import WaveTurbulence.Foundations.Molecule.VineFiniteLabelConnectivity
import Mathlib.Tactic

/-! # Vertex connectivity of the five/seven-atom side and adjoint-cap graphs -/

public section
namespace WaveTurbulence.Vine
open Finset

/-- All edges of a short side have labels in its declared atom set. -/
theorem short_side_endpoints (N k : ℕ) (hk : k=0 ∨ k=1) :
    ∀ e ∈ sideBonds N k,e.1 ∈ sideLabels N k ∧ e.2 ∈ sideLabels N k := by
  rcases hk with rfl | rfl
  · intro e he
    norm_num [sideBonds,railBonds,allocatedRungs,List.range_succ] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [sideLabels]
  · intro e he
    norm_num [sideBonds,railBonds,allocatedRungs,List.range_succ] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [sideLabels,Finset.range_add_one]

/-- Short-side paths avoid every selected atom, including the seven-atom
case that cannot be excluded by branching joints alone after F72. -/
theorem short_side_paths (N k : ℕ) (hN : 9 ≤ N) (hk : k=0 ∨ k=1)
    (z u v : ℕ) (hz : z ∈ sideLabels N k) (hu : u ∈ sideLabels N k)
    (hv : v ∈ sideLabels N k) (huz : u ≠ z) (hvz : v ≠ z) :
    AvoidPath (sideBonds N k) z u v := by
  rcases hk with rfl | rfl
  · exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ (shortSide0_root_paths N hN z u hz hu huz))
      (shortSide0_root_paths N hN z v hz hv hvz)
  · exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ (shortSide1_root_paths N hN z u hz hu huz))
      (shortSide1_root_paths N hN z v hz hv hvz)

/-- Every edge of either short adjoint cap has a declared cap label. -/
theorem short_cap_endpoints (r : ℕ) (hr : r=1 ∨ r=2) :
    ∀ e ∈ capAdjointBonds 9 (r-1),e.1 ∈ capLabels 9 r ∧ e.2 ∈ capLabels 9 r := by
  rcases hr with rfl | rfl
  · intro e he
    norm_num [capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [capLabels,Finset.range_add_one]
  · intro e he
    norm_num [capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [capLabels,Finset.range_add_one]

/-- Each short cap's designated adjoint remains connected after any atom
is removed; the final rung has only its one retained bond. -/
theorem short_cap_paths (r : ℕ) (hr : r=1 ∨ r=2) (z u v : ℕ)
    (hz : z ∈ capLabels 9 r) (hu : u ∈ capLabels 9 r)
    (hv : v ∈ capLabels 9 r) (huz : u ≠ z) (hvz : v ≠ z) :
    AvoidPath (capAdjointBonds 9 (r-1)) z u v := by
  rcases hr with rfl | rfl
  · exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ (shortCap0_root_paths z u hz hu huz))
      (shortCap0_root_paths z v hz hv hvz)
  · exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ (shortCap1_root_paths z u hz hu huz))
      (shortCap1_root_paths z v hz hv hvz)

end WaveTurbulence.Vine
