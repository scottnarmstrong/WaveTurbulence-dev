/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ErasedSpecialTransport
public import WaveTurbulence.Foundations.FinalCount.Algorithm.IncidentBondBound
public import WaveTurbulence.Foundations.FinalCount.Algorithm.SimpleDegreeTwoLocalEdit
public import WaveTurbulence.Foundations.FinalCount.AppBBridgeGraphEffects
import Mathlib.Tactic

/-! # Uniform V2-star and special-count costs for a bridge edit -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem bridge_simple_count_change_abs_le_two (M : Molecule V D) (e : D) (hb : Degen.IsBridge M e) :
    |((simpleDegreeTwoAtoms (eraseBond M e)).card : ℤ)-(simpleDegreeTwoAtoms M).card| ≤ 2 := by
  classical
  let S : Finset V := {M.atom e,M.atom (M.mate e)}
  have hS : S ⊆ M.atoms := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact M.atom_mem _
    · exact mem_singleton.mp hv ▸ M.atom_mem _
  have hout : ∀ v ∈ M.atoms,v ∉ S →
      (SimpleDegreeTwo (eraseBond M e) v ↔ SimpleDegreeTwo M v) := by
    intro v hv hn
    have h1 : M.atom e ≠ v := by intro h; exact hn (by simp [S,h])
    have h2 : M.atom (M.mate e) ≠ v := by intro h; exact hn (by simp [S,h])
    exact eraseBond_simpleDegreeTwo_iff_of_not_endpoint M e h1 h2
  have hh := simpleDegreeTwo_local_edit_abs_le M (eraseBond M e) rfl S hS hout
  simpa only [S,card_pair (appb_bridge_endpoints_distinct M e hb),Nat.cast_ofNat] using hh

theorem bridge_special_count_le_old_add_eight (M : Molecule V D) (hM : M.IsMolecule)
    (e : D) (hb : Degen.IsBridge M e) :
    (appbSpecialBonds (eraseBond M e)).card ≤ (appbSpecialBonds M).card+8 := by
  classical
  let S : Finset V := {M.atom e,M.atom (M.mate e)}
  have hS : S ⊆ M.atoms := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact M.atom_mem _
    · exact mem_singleton.mp hv ▸ M.atom_mem _
  have hsub : appbErasedSpecialBonds M e ⊆ appbSpecialBonds M ∪ appbRemovedBonds M S := by
    intro x hx
    obtain ⟨hx,hxe,hxm,hs⟩ := mem_filter.mp hx
    let xr : {x : D // x ≠ e ∧ x ≠ M.mate e} := ⟨x,hxe,hxm⟩
    have hs' : AppbSpecial (eraseBond M e) xr := (appb_eraseBond_special_iff M e xr).mpr hs
    by_cases hsrc : M.atom x ∈ S
    · exact mem_union_right _ (mem_filter.mpr ⟨hx,Or.inl hsrc⟩)
    by_cases htgt : M.atom (M.mate x) ∈ S
    · exact mem_union_right _ (mem_filter.mpr ⟨hx,Or.inr htgt⟩)
    have h11 : M.atom e ≠ M.atom x := by intro he; exact hsrc (by simp [S,he])
    have h21 : M.atom (M.mate e) ≠ M.atom x := by intro he; exact hsrc (by simp [S,he])
    have h12 : M.atom e ≠ M.atom (M.mate x) := by intro he; exact htgt (by simp [S,he])
    have h22 : M.atom (M.mate e) ≠ M.atom (M.mate x) := by intro he; exact htgt (by simp [S,he])
    have hsold := (eraseBond_special_iff_of_remote_endpoints M e xr h11 h21 h12 h22).mp hs'
    exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,hsold⟩)
  rw [appb_eraseBond_special_count]
  have hbnd := incident_bonds_card_le_four_atoms M hM S hS
  have hc : S.card = 2 := card_pair (appb_bridge_endpoints_distinct M e hb)
  rw [hc] at hbnd
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_left hbnd _))

end WaveTurbulence.Mole.AppbAlgorithm
