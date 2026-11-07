/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.IncidentBondBound
public import WaveTurbulence.Foundations.FinalCount.AppBDeletionSpecialBonds
import Mathlib.Tactic

/-! # Newly special bonds after a literal deletion touch its displayed vertices -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace SpecialDeletion
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

theorem old_of_endpoints_outside (x : Degen.RetainedDart M r.removedAtoms)
    (hsrc : M.atom x.val ∉ P.vertices.image r.vertex)
    (htgt : M.atom (M.mate x.val) ∉ P.vertices.image r.vertex)
    (hs : AppbSpecial r.post x) : AppbSpecial M x.val := by
  obtain ⟨ho,hd1,hd2,a,ha,b,hb,hab,ha1,ha2,hb1,hb2,hcentral,hA,hB⟩ := hs
  have hd1' : M.deg (M.atom x.val) = 3 := (r.post_degree_outside _ hsrc).symm.trans hd1
  have hd2' : M.deg (M.atom (M.mate x.val)) = 3 := (r.post_degree_outside _ htgt).symm.trans hd2
  have ha' := mem_sdiff.mp ha
  have hb' := mem_sdiff.mp hb
  exact ⟨ho,hd1',hd2',a,ha'.1,b,hb'.1,hab,ha1,ha2,hb1,hb2,
    (Degen.bondsBetween_erase_eq M r.removedAtoms x.property.1 x.property.2).symm.trans hcentral,
    (Degen.bondsBetween_erase_eq M r.removedAtoms x.property.1 ha'.2).symm.trans hA,
    (Degen.bondsBetween_erase_eq M r.removedAtoms x.property.2 hb'.2).symm.trans hB⟩

theorem count_le_old_add_displayed (hM : M.IsMolecule) :
    (appbSpecialBonds r.post).card ≤ (appbSpecialBonds M).card+4*P.vertices.card := by
  classical
  let S := P.vertices.image r.vertex
  have hSM : S ⊆ M.atoms := by
    intro v hv
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hv
    exact r.vertex_mem a ha
  have hsub : appbErasureSpecialBonds M r.removedAtoms ⊆ appbSpecialBonds M ∪ appbRemovedBonds M S := by
    intro x hx
    obtain ⟨hx,hx1,hx2,hs⟩ := mem_filter.mp hx
    let xr : Degen.RetainedDart M r.removedAtoms := ⟨x,hx1,hx2⟩
    have hs' : AppbSpecial r.post xr := (appb_eraseAtoms_special_iff M r.removedAtoms xr).mpr hs
    by_cases hsrc : M.atom x ∈ S
    · exact mem_union_right _ (mem_filter.mpr ⟨hx,Or.inl hsrc⟩)
    by_cases htgt : M.atom (M.mate x) ∈ S
    · exact mem_union_right _ (mem_filter.mpr ⟨hx,Or.inr htgt⟩)
    exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,old_of_endpoints_outside r xr hsrc htgt hs'⟩)
  have hc : (appbSpecialBonds r.post).card = (appbErasureSpecialBonds M r.removedAtoms).card :=
    appb_eraseAtoms_special_count M r.removedAtoms
  rw [hc]
  calc
    _ ≤ (appbSpecialBonds M ∪ appbRemovedBonds M S).card := card_le_card hsub
    _ ≤ (appbSpecialBonds M).card+(appbRemovedBonds M S).card := card_union_le _ _
    _ ≤ (appbSpecialBonds M).card+4*S.card := Nat.add_le_add_left (incident_bonds_card_le_four_atoms M hM S hSM) _
    _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_left 4 card_image_le) _

end SpecialDeletion
end WaveTurbulence.Mole.AppbAlgorithm
