/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.Degen.Removal
public import WaveTurbulence.Foundations.Molecule.MoleculeBasic
import Mathlib.Tactic

/-! # Exact incident-bond and self-loop counts for atom deletion -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def bondsOutAt (M : Molecule V D) (v : V) : Finset D := M.bonds.filter fun x => M.atom x = v
def bondsInto (M : Molecule V D) (v : V) : Finset D := M.bonds.filter fun x => M.atom (M.mate x) = v
def selfBondsAt (M : Molecule V D) (v : V) : Finset D := bondsOutAt M v ∩ bondsInto M v
def incidentBondsAt (M : Molecule V D) (v : V) : Finset D := bondsOutAt M v ∪ bondsInto M v

theorem card_bondsOutAt (M : Molecule V D) (v : V) : (bondsOutAt M v).card = M.outdeg v := by
  unfold bondsOutAt Molecule.bonds Molecule.outdeg Molecule.dartsAt
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and, and_comm]

theorem bondsInto_eq_image_mate (M : Molecule V D) (v : V) :
    bondsInto M v = ((M.dartsAt v).filter fun x => M.out x = false).image M.mate := by
  ext x
  simp only [bondsInto, Molecule.bonds, Molecule.dartsAt, mem_filter, mem_univ, true_and, mem_image]
  constructor
  · rintro ⟨hout, hatom⟩
    refine ⟨M.mate x, ⟨hatom, ?_⟩, M.mate_mate x⟩
    rw [M.out_mate, hout]
    rfl
  · rintro ⟨y, ⟨hatom, hout⟩, rfl⟩
    rw [M.out_mate, hout, M.mate_mate]
    exact ⟨rfl, hatom⟩

theorem card_bondsInto (M : Molecule V D) (v : V) : (bondsInto M v).card = M.indeg v := by
  rw [bondsInto_eq_image_mate, card_image_of_injective _ (Mole.mate_injective M)]
  rfl

/-- A loop is counted once as an incident bond and twice in the degree. -/
theorem card_incident_add_self_eq_deg (M : Molecule V D) (v : V) :
    (incidentBondsAt M v).card + (selfBondsAt M v).card = M.deg v := by
  unfold incidentBondsAt selfBondsAt
  rw [card_union_add_card_inter, card_bondsOutAt, card_bondsInto, Mole.outdeg_add_indeg]

/-- Actual outgoing retained bonds reindex the old bonds avoiding removed atoms. -/
theorem card_bonds_eraseAtoms (M : Molecule V D) (Y : Finset V) :
    (eraseAtoms M Y).bonds.card =
      (M.bonds.filter fun x => M.atom x ∉ Y ∧ M.atom (M.mate x) ∉ Y).card := by
  apply card_bij (fun x _ => x.val)
  · intro x hx
    have hout : M.out x.val = true := (mem_filter.mp hx).2
    simp only [mem_filter, Molecule.bonds, mem_univ, true_and]
    exact ⟨hout, x.property⟩
  · intro x _ y _ h
    exact Subtype.ext h
  · intro x hx
    obtain ⟨hxout, hxY⟩ := mem_filter.mp hx
    have hout : M.out x = true := (mem_filter.mp hxout).2
    refine ⟨⟨x, hxY⟩, ?_, rfl⟩
    simp only [Molecule.bonds, mem_filter, mem_univ, true_and]
    exact hout

/-- Exact edge count after one-atom deletion. -/
theorem card_bonds_erase_singleton_add_incident (M : Molecule V D) (v : V) :
    (eraseAtoms M {v}).bonds.card + (incidentBondsAt M v).card = M.bonds.card := by
  rw [card_bonds_eraseAtoms]
  have he : incidentBondsAt M v = M.bonds.filter (fun x => M.atom x = v ∨ M.atom (M.mate x) = v) := by
    ext x
    simp only [incidentBondsAt, bondsOutAt, bondsInto, mem_union, mem_filter]
    tauto
  rw [he]
  have hn : (M.bonds.filter fun x => M.atom x ∉ ({v} : Finset V) ∧ M.atom (M.mate x) ∉ ({v} : Finset V)) =
      M.bonds.filter (fun x => ¬(M.atom x = v ∨ M.atom (M.mate x) = v)) := by
    ext x
    simp only [mem_filter, mem_singleton, not_or]
  rw [hn, add_comm, card_filter_add_card_filter_not]

/-- The outgoing part of the crossing boundary excludes outgoing self-loops. -/
theorem boundary_out_eq (M : Molecule V D) (v : V) :
    ((boundaryDarts M {v}).filter fun x => M.out x = true) = bondsOutAt M v \ bondsInto M v := by
  ext x
  simp only [boundaryDarts, bondsOutAt, bondsInto, Molecule.bonds, mem_filter, mem_univ,
    true_and, mem_singleton, mem_sdiff]
  tauto

/-- Incoming crossing darts are mates of outgoing bonds ending at v, excluding loops. -/
theorem boundary_in_eq (M : Molecule V D) (v : V) :
    ((boundaryDarts M {v}).filter fun x => M.out x = false) =
      (bondsInto M v \ bondsOutAt M v).image M.mate := by
  ext x
  simp only [boundaryDarts, bondsOutAt, bondsInto, Molecule.bonds, mem_filter, mem_univ,
    true_and, mem_singleton, mem_sdiff, mem_image]
  constructor
  · rintro ⟨⟨hatom, hmate⟩, hout⟩
    refine ⟨M.mate x, ⟨⟨?_, ?_⟩, ?_⟩, M.mate_mate x⟩
    · rw [M.out_mate, hout]; rfl
    · simpa only [M.mate_mate] using hatom
    · intro hh
      exact hmate hh.2
  · rintro ⟨y, ⟨⟨hout, hatom⟩, hy⟩, rfl⟩
    have hnot : M.atom y ≠ v := by intro hh; exact hy ⟨hout, hh⟩
    rw [M.mate_mate, M.out_mate, hout]
    exact ⟨⟨hatom, hnot⟩, rfl⟩

/-- The actual cut boundary counts every non-loop incidence once. -/
theorem card_boundary_add_twice_self_eq_deg (M : Molecule V D) (v : V) :
    (boundaryDarts M {v}).card + 2 * (selfBondsAt M v).card = M.deg v := by
  have hpart := card_filter_add_card_filter_not (s := boundaryDarts M {v}) (fun x : D => M.out x = true)
  have hfalse : ((boundaryDarts M {v}).filter fun x => ¬M.out x = true) =
      (boundaryDarts M {v}).filter (fun x => M.out x = false) := by
    ext x
    simp only [mem_filter, Bool.not_eq_true]
  rw [hfalse, boundary_out_eq, boundary_in_eq, card_image_of_injective _ (Mole.mate_injective M)] at hpart
  have hA := card_sdiff_add_card_inter (bondsOutAt M v) (bondsInto M v)
  have hB := card_sdiff_add_card_inter (bondsInto M v) (bondsOutAt M v)
  have hd := Mole.outdeg_add_indeg M v
  rw [← card_bondsOutAt M v, ← card_bondsInto M v] at hd
  change (bondsOutAt M v \ bondsInto M v).card + (bondsOutAt M v ∩ bondsInto M v).card = _ at hA
  rw [inter_comm] at hB
  unfold selfBondsAt
  omega

end WaveTurbulence.Degen
