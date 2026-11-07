/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103DegreeProfiles
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103BetaComplement
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103SelectedCore
import Mathlib.Tactic

/-! # The actual proper initial-profile descendant of a preliminary beta step -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A proper old side with no old degree-three vertex produces the exact
initial profile, including the actual molecule axiom. -/
theorem initial_profile_of_four_regular_two_boundary (M : Molecule V D) (hM : M.IsMolecule)
    (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z))
    (hbridge : ∀ e, ¬ IsBridge M e)
    (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b)
    {v : V} (hv : v ∈ M.atoms) {x y : D} (hx : M.atom x = v) (hy : M.atom y = v)
    (hne : M.atom (M.mate x) ≠ M.atom (M.mate y))
    (U : Finset V) (hU : U ⊆ M.atoms \ {v})
    (hboundary : boundaryDarts M U = {M.mate x,M.mate y})
    (hfull : ∀ a ∈ U, M.deg a = 4) :
    (Mole.induced M U).IsMolecule ∧ TwoThreeProfile (Mole.induced M U) ∧
      (∀ a ∈ U, ∀ b ∈ U, (Mole.induced M U).SameComponent a b) ∧ U.card < M.atoms.card := by
  classical
  have hneD : M.mate x ≠ M.mate y := fun h => hne (congrArg M.atom h)
  have hcard : (boundaryDarts M U).card = 2 := by rw [hboundary,card_pair hneD]
  have hend : ∀ e ∈ boundaryDarts M U, M.atom (M.mate e) = v := by
    intro e he
    rw [hboundary] at he
    simp only [mem_insert,mem_singleton] at he
    rcases he with rfl | rfl
    · simpa only [M.mate_mate] using hx
    · simpa only [M.mate_mate] using hy
  have hconnected := two_boundary_side_induced_connected M hbridge hconn hv U hU hcard hend
  obtain ⟨hxu,hyu,hx3,hy3,hrest⟩ := induced_profile_of_four_and_two_boundary M U hboundary hne hfull
  have hMol := induced_isMolecule_of_connected_degree_ne_four M hM U
    (fun a ha => (mem_sdiff.mp (hU ha)).1) hconnected hxu (by omega : (Mole.induced M U).deg (M.atom (M.mate x)) ≠ 4)
  have hlt : U.card < M.atoms.card := by
    apply card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨fun a ha => (mem_sdiff.mp (hU ha)).1,?_⟩
    intro he
    have hh : v ∈ U := he.symm ▸ hv
    exact (mem_sdiff.mp (hU hh)).2 (mem_singleton_self v)
  exact ⟨hMol,⟨_,hxu,_,hyu,hne,hx3,hy3,hrest⟩,hconnected,hlt⟩

/-- Actual beta preprocessing supplies its two OLD mixed cuts and one
proper connected descendant with the literal original degree profile.
The counting proof may choose the shorter cut independently of this side. -/
theorem exists_initial_profile_side_of_beta (M : Molecule V D) (hM : M.IsMolecule)
    (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z))
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1)
    (hbridge : ∀ e, ¬ IsBridge M e)
    (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b)
    {a b : V} (hab : a ≠ b) (ha3 : M.deg a = 3) (hb3 : M.deg b = 3)
    (hrest : ∀ z ∈ M.atoms, z ≠ a → z ≠ b → M.deg z = 4)
    (hbeta : AdmitsBetaSplit M) :
    ∃ (v : V) (x y r s : D) (U S : Finset V),
      v ∈ M.atoms ∧ M.deg v = 4 ∧
      M.atom x = v ∧ M.atom y = v ∧ M.atom r = v ∧ M.atom s = v ∧
      M.out x = false ∧ M.out y = true ∧ M.out r = false ∧ M.out s = true ∧
      M.dartsAt v = {x,y,r,s} ∧ U ⊆ M.atoms \ {v} ∧
      boundaryDarts M U = {M.mate x,M.mate y} ∧
      boundaryDarts M ((M.atoms \ {v}) \ U) = {M.mate r,M.mate s} ∧
      (S = U ∨ S = (M.atoms \ {v}) \ U) ∧ S ⊆ M.atoms \ {v} ∧
      (Mole.induced M S).IsMolecule ∧ TwoThreeProfile (Mole.induced M S) ∧
      (∀ p ∈ S, ∀ q ∈ S, (Mole.induced M S).SameComponent p q) ∧ S.card < M.atoms.card := by
  classical
  obtain ⟨v,x,y,hd,hv4,hnb,hdisc⟩ := hbeta
  have hv : v ∈ M.atoms := by
    obtain ⟨z,hz,hzv⟩ := mem_map.mp hd.1
    change some z = some v at hzv
    exact Option.some.inj hzv ▸ hz
  have hx : M.atom x = v := Option.some.inj hd.2.2.1
  have hy : M.atom y = v := Option.some.inj hd.2.2.2.1
  obtain ⟨r,s,hr,hs,hro,hso,hxy,hxr,hxs,hyr,hys,hrs,hstar⟩ :=
    exists_remaining_mixed_pair M hM hv hv4 hx hy hd.2.2.2.2.2.1 hd.2.2.2.2.2.2
  obtain ⟨U,hU,hcut,_,_⟩ := exists_old_cut_of_beta_split M hloop hx hy hdisc
  have hTcut := beta_other_side_boundary M hloop hx hy hr hs hxr hxs hyr hys hstar U hU hcut
  have hT : (M.atoms \ {v}) \ U ⊆ M.atoms \ {v} := sdiff_subset
  have hcard : (boundaryDarts M U).card = 2 := by
    rw [hcut,card_pair (fun h => hxy (Mole.mate_injective M h))]
  have hcases := exists_four_regular_side_of_two_boundary M (v := v) hab ha3 hb3 hrest U
    (fun z hz => (mem_sdiff.mp (hU hz)).1) hcard
  rcases hcases with hfull | hfull
  · have hresult := initial_profile_of_four_regular_two_boundary M hM hloop hbridge hconn hv hx hy
      (beta_neighbors_ne M hloop hsimple hx hy hxy) U hU hcut hfull
    exact ⟨v,x,y,r,s,U,U,hv,hv4,hx,hy,hr,hs,hd.2.2.2.2.2.1,hd.2.2.2.2.2.2,hro,hso,hstar,hU,hcut,hTcut,
      Or.inl rfl,hU,hresult⟩
  · have hresult := initial_profile_of_four_regular_two_boundary M hM hloop hbridge hconn hv hr hs
      (beta_neighbors_ne M hloop hsimple hr hs hrs) _ hT hTcut hfull
    exact ⟨v,x,y,r,s,U,(M.atoms \ {v}) \ U,hv,hv4,hx,hy,hr,hs,hd.2.2.2.2.2.1,hd.2.2.2.2.2.2,hro,hso,hstar,hU,hcut,hTcut,
      Or.inr rfl,hT,hresult⟩

end WaveTurbulence.MoleProp
