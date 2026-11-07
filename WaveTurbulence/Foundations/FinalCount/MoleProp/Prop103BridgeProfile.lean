/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103DegreeProfiles
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103SelectedCore
import Mathlib.Tactic

/-! # A preliminary actual bridge side has the literal source degree profile -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- An actual bridge side is connected in its literal induced carrier. -/
theorem bridgeSide_induced_connected (M : Molecule V D) (e : D) (he : IsBridge M e) :
    ∀ a ∈ bridgeSide M e, ∀ b ∈ bridgeSide M e,
      (Mole.induced M (bridgeSide M e)).SameComponent a b := by
  classical
  have hboundary : boundaryDarts (eraseBond M e) (bridgeSide M e) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hold : z.val ∈ boundaryDarts M (bridgeSide M e) := mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hz).2⟩
    rw [boundary_bridgeSide M e he] at hold
    exact z.property.1 (mem_singleton.mp hold)
  intro a ha b hb
  have ha' : Relation.EqvGen (AdjWithoutBond M e) (M.atom e) a := (mem_filter.mp ha).2
  have hb' : Relation.EqvGen (AdjWithoutBond M e) (M.atom e) b := (mem_filter.mp hb).2
  have hp := (eraseBond_sameComponent_iff M e a b).mpr
    (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ ha') hb')
  have hpi := sameComponent_induced_of_boundary_empty (eraseBond M e) (bridgeSide M e) hboundary ha hp
  exact Relation.EqvGen.mono (fun _ _ ⟨z,hza,hzb⟩ => ⟨⟨z.val.val,z.property⟩,hza,hzb⟩) a b hpi

/-- The actual induced profile on a one-bond side with a single old
exceptional degree-three atom. -/
theorem induced_single_boundary_profile (M : Molecule V D) (S : Finset V)
    {e : D} (hb : boundaryDarts M S = {e}) {c : V} (hc : c ∈ S) (hc3 : M.deg c = 3)
    (hrest : ∀ z ∈ S, z ≠ c → M.deg z = 4) :
    TwoThreeProfile (Mole.induced M S) ∨ OneTwoProfile (Mole.induced M S) := by
  classical
  have heS : M.atom e ∈ S := by
    have hh : e ∈ boundaryDarts M S := by rw [hb]; simp
    exact (mem_filter.mp hh).2.1
  have hd (z : V) (hz : z ∈ S) := induced_degree_add_single_boundary M S hb hz
  by_cases hce : c = M.atom e
  · right
    have hcdeg := hd c hc
    rw [hc3,← hce,ite_eq_left rfl] at hcdeg
    refine ⟨c,hc,by omega,?_⟩
    intro z hz hzc
    have hh := hd z hz
    have hez : M.atom e ≠ z := by rw [← hce]; exact (Ne.symm hzc)
    rw [ite_eq_right hez,hrest z hz hzc] at hh
    omega
  · left
    have hdc := hd c hc
    have hde := hd (M.atom e) heS
    rw [ite_eq_right (Ne.symm hce),hc3] at hdc
    rw [ite_eq_left rfl,hrest _ heS (Ne.symm hce)] at hde
    refine ⟨c,hc,M.atom e,heS,hce,by omega,by omega,?_⟩
    intro z hz hzc hze
    have hh := hd z hz
    rw [ite_eq_right (Ne.symm hze),hrest z hz hzc] at hh
    omega

/-- One actual initial bridge produces a proper connected molecule whose
profile is either the original two-degree-three profile or the all-even
single-degree-two profile. No bridge forest classification is assumed. -/
theorem initial_bridge_side_profile (M : Molecule V D) (hM : M.IsMolecule)
    {a b : V} (hab : a ≠ b) (ha3 : M.deg a = 3) (hb3 : M.deg b = 3)
    (hrest : ∀ z ∈ M.atoms, z ≠ a → z ≠ b → M.deg z = 4)
    (e : D) (he : IsBridge M e) :
    let S := bridgeSide M e
    S.card < M.atoms.card ∧ (Mole.induced M S).IsMolecule ∧
      (∀ p ∈ S, ∀ q ∈ S, (Mole.induced M S).SameComponent p q) ∧
      (TwoThreeProfile (Mole.induced M S) ∨ OneTwoProfile (Mole.induced M S)) := by
  classical
  let S := bridgeSide M e
  have hS : S ⊆ M.atoms := bridgeSide_subset M e
  have hb : boundaryDarts M S = {e} := boundary_bridgeSide M e he
  have hodd := exactly_one_degree_three_of_boundary_one M hab ha3 hb3 hrest S hS (by rw [hb,card_singleton])
  have hprofile : TwoThreeProfile (Mole.induced M S) ∨ OneTwoProfile (Mole.induced M S) := by
    by_cases haS : a ∈ S
    · apply induced_single_boundary_profile M S hb haS ha3
      intro z hz hza
      exact hrest z (hS hz) hza (fun h => hodd.mp haS (h ▸ hz))
    · have hbS : b ∈ S := by by_contra hn; exact haS (hodd.mpr hn)
      apply induced_single_boundary_profile M S hb hbS hb3
      intro z hz hzb
      exact hrest z (hS hz) (fun h => haS (h ▸ hz)) hzb
  have hconnected := bridgeSide_induced_connected M e he
  have hMol : (Mole.induced M S).IsMolecule := by
    rcases hprofile with ⟨p,hp,q,hq,hpq,hp3,_⟩ | ⟨p,hp,hp2,_⟩
    · exact induced_isMolecule_of_connected_degree_ne_four M hM S hS hconnected hp (by omega)
    · exact induced_isMolecule_of_connected_degree_ne_four M hM S hS hconnected hp (by omega)
  have hmateNot : M.atom (M.mate e) ∉ S := fun h => he (mem_filter.mp h).2
  have hlt : S.card < M.atoms.card := by
    apply card_lt_card
    exact Finset.ssubset_iff_subset_ne.mpr ⟨hS,fun h => hmateNot (h.symm ▸ M.atom_mem (M.mate e))⟩
  exact ⟨hlt,hMol,hconnected,hprofile⟩

end WaveTurbulence.MoleProp
