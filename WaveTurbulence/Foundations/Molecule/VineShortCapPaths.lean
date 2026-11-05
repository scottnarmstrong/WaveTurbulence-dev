/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineAvoidPaths
public import WaveTurbulence.Foundations.Molecule.VineSideLabels
public import WaveTurbulence.Foundations.Molecule.VineCapBijection
public import WaveTurbulence.Foundations.Molecule.VineCapBonds
import Mathlib.Tactic

/-! # Explicit one-atom-avoiding paths in short cap graphs (F72) -/

public section
namespace WaveTurbulence.Vine
open Finset

/-- Explicit paths for the 5-atom short cap graph. -/
theorem shortCap0_root_paths (z v : ℕ)
    (hz : z ∈ capLabels 9 1) (hv : v ∈ capLabels 9 1) (hvz : v ≠ z) :
    AvoidPath (capAdjointBonds 9 0) z (if z=4 then 5 else 4) v := by
  have hzs : z=4 ∨ z=5 ∨ z=6 ∨ z=9 ∨ z=10 := by simpa [sideLabels,capLabels,Finset.range_add_one,or_comm,or_left_comm,or_assoc] using hz
  have hvs : v=4 ∨ v=5 ∨ v=6 ∨ v=9 ∨ v=10 := by simpa [sideLabels,capLabels,Finset.range_add_one,or_comm,or_left_comm,or_assoc] using hv
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
      exact (Relation.EqvGen.rel (5) (6) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs]⟩)
    · subst v
      exact (Relation.EqvGen.rel (5) (9) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs]⟩)
    · subst v
      exact Relation.EqvGen.trans (5) (6) (10) (Relation.EqvGen.rel (5) (6) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs]⟩) ((Relation.EqvGen.rel (6) (10) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs]⟩))
  · subst z
    have hr : (if (5)=4 then 5 else 4)=4 := by split_ifs <;> omega
    rw [hr]
    rcases hvs with hv | hv | hv | hv | hv
    · subst v
      exact Relation.EqvGen.refl (4)
    · subst v
      exact False.elim (hvz rfl)
    · subst v
      exact (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs]⟩)
    · subst v
      exact Relation.EqvGen.trans (4) (6) (9) (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs]⟩) (Relation.EqvGen.trans (6) (10) (9) (Relation.EqvGen.rel (6) (10) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs]⟩) ((Relation.EqvGen.rel (10) (9) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs]⟩)))
    · subst v
      exact Relation.EqvGen.trans (4) (6) (10) (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs]⟩) ((Relation.EqvGen.rel (6) (10) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs]⟩))
  · subst z
    have hr : (if (6)=4 then 5 else 4)=4 := by split_ifs <;> omega
    rw [hr]
    rcases hvs with hv | hv | hv | hv | hv
    · subst v
      exact Relation.EqvGen.refl (4)
    · subst v
      exact (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs]⟩)
    · subst v
      exact False.elim (hvz rfl)
    · subst v
      exact Relation.EqvGen.trans (4) (5) (9) (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs]⟩) ((Relation.EqvGen.rel (5) (9) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs]⟩))
    · subst v
      exact Relation.EqvGen.trans (4) (5) (10) (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs]⟩) (Relation.EqvGen.trans (5) (9) (10) (Relation.EqvGen.rel (5) (9) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs]⟩) ((Relation.EqvGen.rel (9) (10) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs]⟩)))
  · subst z
    have hr : (if (9)=4 then 5 else 4)=4 := by split_ifs <;> omega
    rw [hr]
    rcases hvs with hv | hv | hv | hv | hv
    · subst v
      exact Relation.EqvGen.refl (4)
    · subst v
      exact (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs]⟩)
    · subst v
      exact (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs]⟩)
    · subst v
      exact False.elim (hvz rfl)
    · subst v
      exact Relation.EqvGen.trans (4) (6) (10) (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs]⟩) ((Relation.EqvGen.rel (6) (10) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs]⟩))
  · subst z
    have hr : (if (10)=4 then 5 else 4)=4 := by split_ifs <;> omega
    rw [hr]
    rcases hvs with hv | hv | hv | hv | hv
    · subst v
      exact Relation.EqvGen.refl (4)
    · subst v
      exact (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs]⟩)
    · subst v
      exact (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs]⟩)
    · subst v
      exact Relation.EqvGen.trans (4) (5) (9) (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs]⟩) ((Relation.EqvGen.rel (5) (9) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs]⟩))
    · subst v
      exact False.elim (hvz rfl)

/-- Explicit paths for the 7-atom short cap graph. -/
theorem shortCap1_root_paths (z v : ℕ)
    (hz : z ∈ capLabels 9 2) (hv : v ∈ capLabels 9 2) (hvz : v ≠ z) :
    AvoidPath (capAdjointBonds 9 1) z (if z=4 then 5 else 4) v := by
  have hzs : z=4 ∨ z=5 ∨ z=6 ∨ z=9 ∨ z=10 ∨ z=11 ∨ z=12 := by simpa [sideLabels,capLabels,Finset.range_add_one,or_comm,or_left_comm,or_assoc] using hz
  have hvs : v=4 ∨ v=5 ∨ v=6 ∨ v=9 ∨ v=10 ∨ v=11 ∨ v=12 := by simpa [sideLabels,capLabels,Finset.range_add_one,or_comm,or_left_comm,or_assoc] using hv
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
      exact (Relation.EqvGen.rel (5) (6) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩)
    · subst v
      exact (Relation.EqvGen.rel (5) (9) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩)
    · subst v
      exact Relation.EqvGen.trans (5) (9) (10) (Relation.EqvGen.rel (5) (9) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (9) (10) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩))
    · subst v
      exact Relation.EqvGen.trans (5) (6) (11) (Relation.EqvGen.rel (5) (6) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (6) (11) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩))
    · subst v
      exact Relation.EqvGen.trans (5) (6) (12) (Relation.EqvGen.rel (5) (6) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (6) (11) (12) (Relation.EqvGen.rel (6) (11) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (11) (12) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩)))
  · subst z
    have hr : (if (5)=4 then 5 else 4)=4 := by split_ifs <;> omega
    rw [hr]
    rcases hvs with hv | hv | hv | hv | hv | hv | hv
    · subst v
      exact Relation.EqvGen.refl (4)
    · subst v
      exact False.elim (hvz rfl)
    · subst v
      exact (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩)
    · subst v
      exact Relation.EqvGen.trans (4) (6) (9) (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (6) (11) (9) (Relation.EqvGen.rel (6) (11) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (11) (9) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩)))
    · subst v
      exact Relation.EqvGen.trans (4) (6) (10) (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (6) (11) (10) (Relation.EqvGen.rel (6) (11) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (11) (12) (10) (Relation.EqvGen.rel (11) (12) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (12) (10) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩))))
    · subst v
      exact Relation.EqvGen.trans (4) (6) (11) (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (6) (11) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩))
    · subst v
      exact Relation.EqvGen.trans (4) (6) (12) (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (6) (11) (12) (Relation.EqvGen.rel (6) (11) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (11) (12) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩)))
  · subst z
    have hr : (if (6)=4 then 5 else 4)=4 := by split_ifs <;> omega
    rw [hr]
    rcases hvs with hv | hv | hv | hv | hv | hv | hv
    · subst v
      exact Relation.EqvGen.refl (4)
    · subst v
      exact (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩)
    · subst v
      exact False.elim (hvz rfl)
    · subst v
      exact Relation.EqvGen.trans (4) (5) (9) (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (5) (9) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩))
    · subst v
      exact Relation.EqvGen.trans (4) (5) (10) (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (5) (9) (10) (Relation.EqvGen.rel (5) (9) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (9) (10) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩)))
    · subst v
      exact Relation.EqvGen.trans (4) (5) (11) (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (5) (9) (11) (Relation.EqvGen.rel (5) (9) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (9) (11) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩)))
    · subst v
      exact Relation.EqvGen.trans (4) (5) (12) (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (5) (9) (12) (Relation.EqvGen.rel (5) (9) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (9) (10) (12) (Relation.EqvGen.rel (9) (10) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (10) (12) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩))))
  · subst z
    have hr : (if (9)=4 then 5 else 4)=4 := by split_ifs <;> omega
    rw [hr]
    rcases hvs with hv | hv | hv | hv | hv | hv | hv
    · subst v
      exact Relation.EqvGen.refl (4)
    · subst v
      exact (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩)
    · subst v
      exact (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩)
    · subst v
      exact False.elim (hvz rfl)
    · subst v
      exact Relation.EqvGen.trans (4) (6) (10) (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (6) (11) (10) (Relation.EqvGen.rel (6) (11) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (11) (12) (10) (Relation.EqvGen.rel (11) (12) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (12) (10) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩))))
    · subst v
      exact Relation.EqvGen.trans (4) (6) (11) (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (6) (11) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩))
    · subst v
      exact Relation.EqvGen.trans (4) (6) (12) (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (6) (11) (12) (Relation.EqvGen.rel (6) (11) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (11) (12) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩)))
  · subst z
    have hr : (if (10)=4 then 5 else 4)=4 := by split_ifs <;> omega
    rw [hr]
    rcases hvs with hv | hv | hv | hv | hv | hv | hv
    · subst v
      exact Relation.EqvGen.refl (4)
    · subst v
      exact (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩)
    · subst v
      exact (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩)
    · subst v
      exact Relation.EqvGen.trans (4) (5) (9) (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (5) (9) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩))
    · subst v
      exact False.elim (hvz rfl)
    · subst v
      exact Relation.EqvGen.trans (4) (6) (11) (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (6) (11) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩))
    · subst v
      exact Relation.EqvGen.trans (4) (6) (12) (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (6) (11) (12) (Relation.EqvGen.rel (6) (11) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (11) (12) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩)))
  · subst z
    have hr : (if (11)=4 then 5 else 4)=4 := by split_ifs <;> omega
    rw [hr]
    rcases hvs with hv | hv | hv | hv | hv | hv | hv
    · subst v
      exact Relation.EqvGen.refl (4)
    · subst v
      exact (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩)
    · subst v
      exact (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩)
    · subst v
      exact Relation.EqvGen.trans (4) (5) (9) (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (5) (9) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩))
    · subst v
      exact Relation.EqvGen.trans (4) (5) (10) (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (5) (9) (10) (Relation.EqvGen.rel (5) (9) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (9) (10) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩)))
    · subst v
      exact False.elim (hvz rfl)
    · subst v
      exact Relation.EqvGen.trans (4) (5) (12) (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (5) (9) (12) (Relation.EqvGen.rel (5) (9) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (9) (10) (12) (Relation.EqvGen.rel (9) (10) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (10) (12) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩))))
  · subst z
    have hr : (if (12)=4 then 5 else 4)=4 := by split_ifs <;> omega
    rw [hr]
    rcases hvs with hv | hv | hv | hv | hv | hv | hv
    · subst v
      exact Relation.EqvGen.refl (4)
    · subst v
      exact (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩)
    · subst v
      exact (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩)
    · subst v
      exact Relation.EqvGen.trans (4) (5) (9) (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (5) (9) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩))
    · subst v
      exact Relation.EqvGen.trans (4) (5) (10) (Relation.EqvGen.rel (4) (5) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) (Relation.EqvGen.trans (5) (9) (10) (Relation.EqvGen.rel (5) (9) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (9) (10) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩)))
    · subst v
      exact Relation.EqvGen.trans (4) (6) (11) (Relation.EqvGen.rel (4) (6) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩) ((Relation.EqvGen.rel (6) (11) ⟨by omega,by omega,by simp [EdgeAdj,capAdjointBonds,capTriangleBonds,railBonds,allocatedRungs,List.range_succ]⟩))
    · subst v
      exact False.elim (hvz rfl)

end WaveTurbulence.Vine
