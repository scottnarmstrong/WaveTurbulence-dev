/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DeletionFibers
import Mathlib.Tactic

/-! # Actual deleted-label images are determined by one atom's incidences -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

abbrev IncidentDart (M : Molecule V D) (v : V) := {x : D // M.atom x = v}

def starLabels (M : Molecule V D) (v : V) {K : Type*} (κ : D → K) : IncidentDart M v → K :=
  fun x => κ x.val

/-- Reconstruct each removed half-edge label from the incidence at v.
This chooses the actual endpoint of the removed bond, not an auxiliary label. -/
noncomputable def deletedFromStar (M : Molecule V D) (v : V) {K : Type*}
    (q : IncidentDart M v → K) (x : DeletedDart M {v}) : K := by
  classical
  by_cases hx : M.atom x.val = v
  · exact q ⟨x.val,hx⟩
  · have hm : M.atom (M.mate x.val) = v := by
      by_contra hn
      exact x.property ⟨by simpa only [mem_singleton] using hx,by simpa only [mem_singleton] using hn⟩
    exact q ⟨M.mate x.val,hm⟩

theorem deletedFromStar_starLabels (M : Molecule V D) (v : V) {K : Type*}
    (κ : D → K) (hb : ∀ x, κ (M.mate x) = κ x) :
    deletedFromStar M v (starLabels M v κ) = deletedLabels M {v} κ := by
  classical
  funext x
  unfold deletedFromStar starLabels deletedLabels
  split_ifs
  · rfl
  · exact hb x.val

/-- Bond consistency removes duplicated mate labels from the local counting
problem, including loops. No false independent choice is counted at a mate. -/
theorem card_deletedLabels_image_le_starLabels_image (M : Molecule V D) (v : V)
    {K : Type*} [DecidableEq K] (S : Finset (D → K))
    (hb : ∀ κ ∈ S, ∀ x, κ (M.mate x) = κ x) :
    (S.image (deletedLabels M {v})).card ≤ (S.image (starLabels M v)).card := by
  classical
  have he : S.image (deletedLabels M {v}) =
      (S.image (starLabels M v)).image (deletedFromStar M v) := by
    rw [image_image]
    apply image_congr
    intro κ hκ
    exact (deletedFromStar_starLabels M v κ (hb κ hκ)).symm
  rw [he]
  exact card_image_le

/-- The genuine incident-dart carrier has exactly the actual degree. -/
theorem card_incidentDart (M : Molecule V D) (v : V) :
    Fintype.card (IncidentDart M v) = M.deg v := by
  simp only [IncidentDart,Molecule.deg,Molecule.dartsAt,Fintype.card_subtype]

theorem starLabels_injective_on_deleted_fibers (M : Molecule V D) (v : V)
    {K : Type*} {κ κ' : D → K} (hb : ∀ x, κ (M.mate x) = κ x)
    (hb' : ∀ x, κ' (M.mate x) = κ' x)
    (h : starLabels M v κ = starLabels M v κ') :
    deletedLabels M {v} κ = deletedLabels M {v} κ' := by
  rw [← deletedFromStar_starLabels M v κ hb,← deletedFromStar_starLabels M v κ' hb',h]

end WaveTurbulence.MoleProp
