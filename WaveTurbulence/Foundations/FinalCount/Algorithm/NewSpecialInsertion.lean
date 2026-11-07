/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.AddedStarTransport
public import WaveTurbulence.Foundations.FinalCount.Algorithm.IncidentBondBound
public import WaveTurbulence.Foundations.FinalCount.AppBAddedSpecialBonds
import Mathlib.Tactic

/-! # Uniform special-bond creation bound for the actual inserted bond -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem addBond_old_special_iff_of_remote (M : Molecule V D) {a b : V}
    (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) (x : D)
    (h11 : a ≠ M.atom x) (h21 : b ≠ M.atom x)
    (h12 : a ≠ M.atom (M.mate x)) (h22 : b ≠ M.atom (M.mate x)) :
    AppbSpecial (addBond M a b) (Sum.inl x) ↔ AppbSpecial M x := by
  classical
  have hp1 (v : V) : appbAddedPairCount M a b (M.atom x) v = M.bondsBetween (M.atom x) v := by
    unfold appbAddedPairCount
    simpa only [appb_addBond_bondsBetween] using addBond_bondsBetween_of_remote M a b h11 h21 v
  have hp2 (v : V) : appbAddedPairCount M a b (M.atom (M.mate x)) v = M.bondsBetween (M.atom (M.mate x)) v := by
    unfold appbAddedPairCount
    simpa only [appb_addBond_bondsBetween] using addBond_bondsBetween_of_remote M a b h12 h22 v
  have hA : insert a (insert b M.atoms) = M.atoms := addBond_atoms_of_mem M ha hb
  rw [appb_addBond_special_old_iff]
  simp only [AppbAddedSpecialEnds,AppbSpecial,h11,h21,h12,h22,ite_false,add_zero,hp1,hp2,hA]

theorem insertion_special_count_le_old_add_nine (M : Molecule V D) (hM : M.IsMolecule)
    {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) (hab : a ≠ b) :
    (appbSpecialBonds (addBond M a b)).card ≤ (appbSpecialBonds M).card+9 := by
  classical
  let S : Finset V := {a,b}
  have hS : S ⊆ M.atoms := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact ha
    · exact mem_singleton.mp hv ▸ hb
  have hsub : appbAddedOldSpecialBonds M a b ⊆ appbSpecialBonds M ∪ appbRemovedBonds M S := by
    intro x hx
    obtain ⟨hx,hs⟩ := mem_filter.mp hx
    have hs' := (appb_addBond_special_old_iff M a b x).mpr ⟨(mem_filter.mp hx).2,hs⟩
    by_cases hsrc : M.atom x ∈ S
    · exact mem_union_right _ (mem_filter.mpr ⟨hx,Or.inl hsrc⟩)
    by_cases htgt : M.atom (M.mate x) ∈ S
    · exact mem_union_right _ (mem_filter.mpr ⟨hx,Or.inr htgt⟩)
    have h11 : a ≠ M.atom x := by intro he; exact hsrc (by simp [S,he])
    have h21 : b ≠ M.atom x := by intro he; exact hsrc (by simp [S,he])
    have h12 : a ≠ M.atom (M.mate x) := by intro he; exact htgt (by simp [S,he])
    have h22 : b ≠ M.atom (M.mate x) := by intro he; exact htgt (by simp [S,he])
    exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,(addBond_old_special_iff_of_remote M ha hb x h11 h21 h12 h22).mp hs'⟩)
  have hold : (appbAddedOldSpecialBonds M a b).card ≤ (appbSpecialBonds M).card+8 := by
    have hi := incident_bonds_card_le_four_atoms M hM S hS
    have hc : S.card = 2 := card_pair hab
    rw [hc] at hi
    exact (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_left hi _))
  have hnew : (appbAddedNewSpecialBonds M a b).card ≤ 1 := by
    unfold appbAddedNewSpecialBonds
    split_ifs <;> simp
  rw [appb_addBond_special_count]
  omega

end WaveTurbulence.Mole.AppbAlgorithm
