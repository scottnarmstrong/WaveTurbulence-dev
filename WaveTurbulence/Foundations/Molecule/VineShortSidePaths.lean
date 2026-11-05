/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineAvoidPaths
public import WaveTurbulence.Foundations.Molecule.VineSideLabels
public import WaveTurbulence.Foundations.Molecule.VineCapBijection
public import WaveTurbulence.Foundations.Molecule.VineCapBonds
import Mathlib.Tactic

/-! # Explicit one-atom-avoiding paths in short side graphs (F72) -/

public section
namespace WaveTurbulence.Vine
open Finset

/-- Explicit paths for the 5-atom short side graph. -/
theorem shortSide0_root_paths (N : ℕ) (_hN : 9 ≤ N) (z v : ℕ)
    (hz : z ∈ sideLabels N 0) (hv : v ∈ sideLabels N 0) (hvz : v ≠ z) :
    AvoidPath (sideBonds N 0) z (if z=4 then 5 else 4) v := by
  have hzs : z=4 ∨ z=5 ∨ z=6 ∨ z=7 ∨ z=8 := by simpa [sideLabels,capLabels,Finset.range_add_one,or_comm,or_left_comm,or_assoc] using hz
  have hvs : v=4 ∨ v=5 ∨ v=6 ∨ v=7 ∨ v=8 := by simpa [sideLabels,capLabels,Finset.range_add_one,or_comm,or_left_comm,or_assoc] using hv
  rcases hzs with hz | hz | hz | hz | hz
  · subst z
    have hr : (if (4)=4 then 5 else 4)=5 := by split_ifs <;> omega
    rw [hr]
    rcases hvs with hv | hv | hv | hv | hv
    · subst v
      exact False.elim (hvz rfl)
    · subst v
      exact Relation.EqvGen.refl (5)
    · subst v
      exact (Relation.EqvGen.rel (5) (6) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs]⟩)
    · subst v
      exact (Relation.EqvGen.rel (5) (7) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs]⟩)
    · subst v
      exact Relation.EqvGen.trans (5) (6) (8) (Relation.EqvGen.rel (5) (6) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs]⟩) ((Relation.EqvGen.rel (6) (8) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs]⟩))
  · subst z
    have hr : (if (5)=4 then 5 else 4)=4 := by split_ifs <;> omega
    rw [hr]
    rcases hvs with hv | hv | hv | hv | hv
    · subst v
      exact Relation.EqvGen.refl (4)
    · subst v
      exact False.elim (hvz rfl)
    · subst v
      exact (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs]⟩)
    · subst v
      exact Relation.EqvGen.trans (4) (6) (7) (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs]⟩) (Relation.EqvGen.trans (6) (8) (7) (Relation.EqvGen.rel (6) (8) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs]⟩) ((Relation.EqvGen.rel (8) (7) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs]⟩)))
    · subst v
      exact Relation.EqvGen.trans (4) (6) (8) (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs]⟩) ((Relation.EqvGen.rel (6) (8) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs]⟩))
  · subst z
    have hr : (if (6)=4 then 5 else 4)=4 := by split_ifs <;> omega
    rw [hr]
    rcases hvs with hv | hv | hv | hv | hv
    · subst v
      exact Relation.EqvGen.refl (4)
    · subst v
      exact (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs]⟩)
    · subst v
      exact False.elim (hvz rfl)
    · subst v
      exact Relation.EqvGen.trans (4) (5) (7) (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs]⟩) ((Relation.EqvGen.rel (5) (7) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs]⟩))
    · subst v
      exact Relation.EqvGen.trans (4) (5) (8) (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs]⟩) (Relation.EqvGen.trans (5) (7) (8) (Relation.EqvGen.rel (5) (7) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs]⟩) ((Relation.EqvGen.rel (7) (8) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs]⟩)))
  · subst z
    have hr : (if (7)=4 then 5 else 4)=4 := by split_ifs <;> omega
    rw [hr]
    rcases hvs with hv | hv | hv | hv | hv
    · subst v
      exact Relation.EqvGen.refl (4)
    · subst v
      exact (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs]⟩)
    · subst v
      exact (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs]⟩)
    · subst v
      exact False.elim (hvz rfl)
    · subst v
      exact Relation.EqvGen.trans (4) (6) (8) (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs]⟩) ((Relation.EqvGen.rel (6) (8) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs]⟩))
  · subst z
    have hr : (if (8)=4 then 5 else 4)=4 := by split_ifs <;> omega
    rw [hr]
    rcases hvs with hv | hv | hv | hv | hv
    · subst v
      exact Relation.EqvGen.refl (4)
    · subst v
      exact (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs]⟩)
    · subst v
      exact (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs]⟩)
    · subst v
      exact Relation.EqvGen.trans (4) (5) (7) (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs]⟩) ((Relation.EqvGen.rel (5) (7) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs]⟩))
    · subst v
      exact False.elim (hvz rfl)

/-- Explicit paths for the 7-atom short side graph. -/
theorem shortSide1_root_paths (N : ℕ) (_hN : 9 ≤ N) (z v : ℕ)
    (hz : z ∈ sideLabels N 1) (hv : v ∈ sideLabels N 1) (hvz : v ≠ z) :
    AvoidPath (sideBonds N 1) z (if z=4 then 5 else 4) v := by
  have hzs : z=4 ∨ z=5 ∨ z=6 ∨ z=7 ∨ z=8 ∨ z=N ∨ z=N+1 := by simpa [sideLabels,capLabels,Finset.range_add_one,or_comm,or_left_comm,or_assoc] using hz
  have hvs : v=4 ∨ v=5 ∨ v=6 ∨ v=7 ∨ v=8 ∨ v=N ∨ v=N+1 := by simpa [sideLabels,capLabels,Finset.range_add_one,or_comm,or_left_comm,or_assoc] using hv
  rcases hzs with hz | hz | hz | hz | hz | hz | hz
  · subst z
    have hr : (if (4)=4 then 5 else 4)=5 := by split_ifs <;> omega
    rw [hr]
    rcases hvs with hv | hv | hv | hv | hv | hv | hv
    · subst v
      exact False.elim (hvz rfl)
    · subst v
      exact Relation.EqvGen.refl (5)
    · subst v
      exact (Relation.EqvGen.rel (5) (6) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩)
    · subst v
      exact Relation.EqvGen.trans (5) (N) (7) (Relation.EqvGen.rel (5) (N) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (N) (7) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩))
    · subst v
      exact Relation.EqvGen.trans (5) (6) (8) (Relation.EqvGen.rel (5) (6) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (6) (N+1) (8) (Relation.EqvGen.rel (6) (N+1) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (N+1) (8) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩)))
    · subst v
      exact (Relation.EqvGen.rel (5) (N) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩)
    · subst v
      exact Relation.EqvGen.trans (5) (6) (N+1) (Relation.EqvGen.rel (5) (6) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (6) (N+1) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩))
  · subst z
    have hr : (if (5)=4 then 5 else 4)=4 := by split_ifs <;> omega
    rw [hr]
    rcases hvs with hv | hv | hv | hv | hv | hv | hv
    · subst v
      exact Relation.EqvGen.refl (4)
    · subst v
      exact False.elim (hvz rfl)
    · subst v
      exact (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩)
    · subst v
      exact Relation.EqvGen.trans (4) (6) (7) (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (6) (N+1) (7) (Relation.EqvGen.rel (6) (N+1) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (N+1) (8) (7) (Relation.EqvGen.rel (N+1) (8) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (8) (7) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩))))
    · subst v
      exact Relation.EqvGen.trans (4) (6) (8) (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (6) (N+1) (8) (Relation.EqvGen.rel (6) (N+1) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (N+1) (8) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩)))
    · subst v
      exact Relation.EqvGen.trans (4) (6) (N) (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (6) (N+1) (N) (Relation.EqvGen.rel (6) (N+1) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (N+1) (N) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩)))
    · subst v
      exact Relation.EqvGen.trans (4) (6) (N+1) (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (6) (N+1) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩))
  · subst z
    have hr : (if (6)=4 then 5 else 4)=4 := by split_ifs <;> omega
    rw [hr]
    rcases hvs with hv | hv | hv | hv | hv | hv | hv
    · subst v
      exact Relation.EqvGen.refl (4)
    · subst v
      exact (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩)
    · subst v
      exact False.elim (hvz rfl)
    · subst v
      exact Relation.EqvGen.trans (4) (5) (7) (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (5) (N) (7) (Relation.EqvGen.rel (5) (N) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (N) (7) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩)))
    · subst v
      exact Relation.EqvGen.trans (4) (5) (8) (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (5) (N) (8) (Relation.EqvGen.rel (5) (N) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (N) (7) (8) (Relation.EqvGen.rel (N) (7) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (7) (8) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩))))
    · subst v
      exact Relation.EqvGen.trans (4) (5) (N) (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (5) (N) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩))
    · subst v
      exact Relation.EqvGen.trans (4) (5) (N+1) (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (5) (N) (N+1) (Relation.EqvGen.rel (5) (N) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (N) (N+1) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩)))
  · subst z
    have hr : (if (7)=4 then 5 else 4)=4 := by split_ifs <;> omega
    rw [hr]
    rcases hvs with hv | hv | hv | hv | hv | hv | hv
    · subst v
      exact Relation.EqvGen.refl (4)
    · subst v
      exact (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩)
    · subst v
      exact (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩)
    · subst v
      exact False.elim (hvz rfl)
    · subst v
      exact Relation.EqvGen.trans (4) (6) (8) (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (6) (N+1) (8) (Relation.EqvGen.rel (6) (N+1) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (N+1) (8) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩)))
    · subst v
      exact Relation.EqvGen.trans (4) (5) (N) (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (5) (N) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩))
    · subst v
      exact Relation.EqvGen.trans (4) (6) (N+1) (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (6) (N+1) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩))
  · subst z
    have hr : (if (8)=4 then 5 else 4)=4 := by split_ifs <;> omega
    rw [hr]
    rcases hvs with hv | hv | hv | hv | hv | hv | hv
    · subst v
      exact Relation.EqvGen.refl (4)
    · subst v
      exact (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩)
    · subst v
      exact (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩)
    · subst v
      exact Relation.EqvGen.trans (4) (5) (7) (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (5) (N) (7) (Relation.EqvGen.rel (5) (N) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (N) (7) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩)))
    · subst v
      exact False.elim (hvz rfl)
    · subst v
      exact Relation.EqvGen.trans (4) (5) (N) (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (5) (N) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩))
    · subst v
      exact Relation.EqvGen.trans (4) (6) (N+1) (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (6) (N+1) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩))
  · subst z
    have hr : (if (N)=4 then 5 else 4)=4 := by split_ifs <;> omega
    rw [hr]
    rcases hvs with hv | hv | hv | hv | hv | hv | hv
    · subst v
      exact Relation.EqvGen.refl (4)
    · subst v
      exact (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩)
    · subst v
      exact (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩)
    · subst v
      exact Relation.EqvGen.trans (4) (6) (7) (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (6) (N+1) (7) (Relation.EqvGen.rel (6) (N+1) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (N+1) (8) (7) (Relation.EqvGen.rel (N+1) (8) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (8) (7) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩))))
    · subst v
      exact Relation.EqvGen.trans (4) (6) (8) (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (6) (N+1) (8) (Relation.EqvGen.rel (6) (N+1) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (N+1) (8) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩)))
    · subst v
      exact False.elim (hvz rfl)
    · subst v
      exact Relation.EqvGen.trans (4) (6) (N+1) (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (6) (N+1) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩))
  · subst z
    have hr : (if (N+1)=4 then 5 else 4)=4 := by split_ifs <;> omega
    rw [hr]
    rcases hvs with hv | hv | hv | hv | hv | hv | hv
    · subst v
      exact Relation.EqvGen.refl (4)
    · subst v
      exact (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩)
    · subst v
      exact (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩)
    · subst v
      exact Relation.EqvGen.trans (4) (5) (7) (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (5) (N) (7) (Relation.EqvGen.rel (5) (N) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (N) (7) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩)))
    · subst v
      exact Relation.EqvGen.trans (4) (5) (8) (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (5) (N) (8) (Relation.EqvGen.rel (5) (N) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (N) (7) (8) (Relation.EqvGen.rel (N) (7) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (7) (8) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩))))
    · subst v
      exact Relation.EqvGen.trans (4) (5) (N) (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (5) (N) ⟨by omega,by omega,by simp [EdgeAdj,sideBonds,railBonds,allocatedRungs,List.range_succ]⟩))
    · subst v
      exact False.elim (hvz rfl)

end WaveTurbulence.Vine
