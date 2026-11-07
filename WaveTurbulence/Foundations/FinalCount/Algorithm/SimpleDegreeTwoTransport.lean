/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SimpleDegreeTwo
public import WaveTurbulence.Foundations.FinalCount.AppBDeletionDegrees
public import WaveTurbulence.Foundations.FinalCount.Degen.LadderRestriction
public import WaveTurbulence.Foundations.Molecule.MoleculeBondsBetween
import Mathlib.Tactic

/-! # V2-star is unchanged away from an actual deletion's displayed vertices -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

theorem neighbor_not_removed_of_outside {v b : V} (hv : v ∉ P.vertices.image r.vertex)
    (hp : 0 < M.bondsBetween v b) : b ∉ r.removedAtoms := by
  intro hb
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hb
  have hp' : 0 < M.bondsBetween (r.vertex i) v := by rw [bondsBetween_symm]; exact hp
  obtain ⟨j,hj,he⟩ := r.neighbor_mem_vertices i hi hp'
  exact hv (mem_image.mpr ⟨j,hj,he.symm⟩)

theorem simpleDegreeTwo_iff_outside {v : V} (hv : v ∉ P.vertices.image r.vertex) :
    SimpleDegreeTwo r.post v ↔ SimpleDegreeTwo M v := by
  have hnv : v ∉ r.removedAtoms := by
    intro h
    obtain ⟨i,hi,rfl⟩ := mem_image.mp h
    exact hv (mem_image_of_mem _ (mem_union_left _ hi))
  have hd := r.post_degree_outside v hv
  constructor
  · rintro ⟨hdeg,b,hb,c,hc,hvb,hvc,hbc,hmb,hmc⟩
    have hb' : b ∈ M.atoms ∧ b ∉ r.removedAtoms := mem_sdiff.mp hb
    have hc' : c ∈ M.atoms ∧ c ∉ r.removedAtoms := mem_sdiff.mp hc
    have hmb' := Degen.bondsBetween_erase_eq M r.removedAtoms hnv hb'.2
    have hmc' := Degen.bondsBetween_erase_eq M r.removedAtoms hnv hc'.2
    exact ⟨hd ▸ hdeg,b,hb'.1,c,hc'.1,hvb,hvc,hbc,hmb'.symm.trans hmb,hmc'.symm.trans hmc⟩
  · rintro ⟨hdeg,b,hb,c,hc,hvb,hvc,hbc,hmb,hmc⟩
    have hnb := neighbor_not_removed_of_outside r hv (by rw [hmb]; decide)
    have hnc := neighbor_not_removed_of_outside r hv (by rw [hmc]; decide)
    refine ⟨hd.symm ▸ hdeg,b,mem_sdiff.mpr ⟨hb,hnb⟩,c,mem_sdiff.mpr ⟨hc,hnc⟩,hvb,hvc,hbc,?_,?_⟩
    · exact (Degen.bondsBetween_erase_eq M r.removedAtoms hnv hnb).trans hmb
    · exact (Degen.bondsBetween_erase_eq M r.removedAtoms hnv hnc).trans hmc

end AppbRealization
end WaveTurbulence.Mole.AppbAlgorithm
