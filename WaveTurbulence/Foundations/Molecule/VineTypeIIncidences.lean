/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineTwoIncidenceExtraction
public import WaveTurbulence.Foundations.Molecule.VineRealizationGroups
import Mathlib.Tactic

/-! # Actual doubled incidences in type-I vine ingredients -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- A type-I ingredient supplies two distinct actual darts between its
joints, without an incidence-witness assumption. -/
theorem typeI_twoIncidences {M : Molecule V D} {S : Finset V} {a b : V}
    (h : M.IsVine .I S a b) : Nonempty (TwoIncidences M a b) := by
  obtain ⟨_hB,⟨R⟩⟩ := isVine_iff_realization.mp h
  have hk : R.k=[] := List.length_eq_zero_iff.mp R.length_eq
  have hlabels : mappedGroupNeighbors M S R.f a={R.f b}+{R.f b} := by
    rw [R.neighbors h.1.2.1]
    have ha : R.f a=0 ∨ R.f a=1 := by
      have hm : R.f a ∈ ({0,1} : Finset ℕ) := R.joints_eq ▸ mem_insert_self _ _
      simpa only [mem_insert,mem_singleton] using hm
    have hb : R.f b=0 ∨ R.f b=1 := by
      have hm : R.f b ∈ ({0,1} : Finset ℕ) := R.joints_eq ▸ mem_insert_of_mem (mem_singleton_self _)
      simpa only [mem_insert,mem_singleton] using hm
    have hne : R.f a ≠ R.f b := fun he => h.1.2.2.2.1 (R.injOn h.1.2.1 h.1.2.2.1 he)
    rcases ha with ha | ha
    · have hb : R.f b=1 := by omega
      rw [ha,hb,hk]
      simp [VineType.expand,VineType.template,edgeListNeighbors,bondNeighbors_pair]
    · have hb : R.f b=0 := by omega
      rw [ha,hb,hk]
      simp [VineType.expand,VineType.template,edgeListNeighbors,bondNeighbors_pair]
  apply exists_twoIncidences_of_neighbors M S R.f R.injOn a (fun _ => b)
    (fun _ => h.1.2.2.1) rfl
  rw [hlabels,Fin.univ_val_map]
  rfl

end WaveTurbulence.Vine
