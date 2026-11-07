/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.LowDegreeConnectivity
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103CutParity
import Mathlib.Tactic

/-! # A two-bond side is connected after deleting its common exterior atom -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Paths in a component-closed atom set lift to the actual induced graph. -/
theorem sameComponent_induced_of_boundary_empty (M : Molecule V D) (U : Finset V)
    (hboundary : boundaryDarts M U = ∅) {a b : V} (ha : a ∈ U)
    (hp : M.SameComponent a b) : (Mole.induced M U).SameComponent a b := by
  have hclosed (a b : V) (hab : M.Adj a b) (ha : a ∈ U) : b ∈ U := by
    by_contra hb
    obtain ⟨e,hea,heb⟩ := hab
    have hh : e ∈ boundaryDarts M U :=
      mem_filter.mpr ⟨mem_univ _,hea.symm ▸ ha,heb.symm ▸ hb⟩
    rw [hboundary] at hh
    simpa using hh
  have haux (a b : V) (hp : M.SameComponent a b) : a ∈ U →
      (Mole.induced M U).SameComponent a b := by
    induction hp with
    | rel a b hab =>
      intro ha
      have hb := hclosed a b hab ha
      obtain ⟨e,hea,heb⟩ := hab
      exact Relation.EqvGen.rel _ _ ⟨⟨e,hea.symm ▸ ha,heb.symm ▸ hb⟩,hea,heb⟩
    | refl a => intro _; exact Relation.EqvGen.refl a
    | symm a b hp ih =>
      intro hb
      have ha := (sameComponent_mem_iff_of_boundary_empty M U hboundary hp).mpr hb
      exact Relation.EqvGen.symm _ _ (ih ha)
    | trans a b c hp _ ih1 ih2 =>
      intro ha
      have hb := (sameComponent_mem_iff_of_boundary_empty M U hboundary hp).mp ha
      exact Relation.EqvGen.trans _ _ _ (ih1 ha) (ih2 hb)
  exact haux a b hp ha

/-- OLD bridgelessness forces a two-bond side attached only to v to be
connected after deleting v. There is no articulation shortcut or assumed
component certificate. -/
theorem two_boundary_side_connected_after_erase (M : Molecule V D)
    (hbridge : ∀ e, ¬ IsBridge M e)
    (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b)
    {v : V} (hv : v ∈ M.atoms) (U : Finset V) (hU : U ⊆ M.atoms \ {v})
    (hcard : (boundaryDarts M U).card = 2)
    (hend : ∀ e ∈ boundaryDarts M U, M.atom (M.mate e) = v) :
    ∀ a ∈ U, ∀ b ∈ U, (eraseAtoms M {v}).SameComponent a b := by
  classical
  have hvnot : v ∉ U := fun h => (mem_sdiff.mp (hU h)).2 (mem_singleton_self v)
  have hstep (a b : V) (hab : ResidualAdj M {v} a b) : a ∈ U ↔ b ∈ U := by
    obtain ⟨ha,hb,e,hea,heb⟩ := hab
    constructor
    · intro hau
      by_contra hbu
      have heU : e ∈ boundaryDarts M U := mem_filter.mpr ⟨mem_univ _,hea.symm ▸ hau,heb.symm ▸ hbu⟩
      have hvb := (hend e heU).symm.trans heb
      exact hb (by simpa only [mem_singleton] using hvb.symm)
    · intro hbu
      by_contra hau
      have heU : M.mate e ∈ boundaryDarts M U := by
        apply mem_filter.mpr
        refine ⟨mem_univ _,heb.symm ▸ hbu,?_⟩
        simpa only [M.mate_mate,hea] using hau
      have hva : a = v := hea.symm.trans (by simpa only [M.mate_mate] using hend (M.mate e) heU)
      exact ha (by simpa only [mem_singleton] using hva)
  have hpath (a b : V) (hab : Relation.EqvGen (ResidualAdj M {v}) a b) : a ∈ U ↔ b ∈ U := by
    induction hab with
    | rel a b h => exact hstep a b h
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  have hboundary (a : V) (ha : a ∈ U) :
      boundaryDarts M (residualComponent M {v} a) = boundaryDarts M U := by
    have ha' := mem_sdiff.mp (hU ha)
    have han : a ≠ v := by simpa only [mem_singleton] using ha'.2
    have hnew := residualComponent_mem_newComponents_of_sameComponent M hv ha'.1 han
      (hconn a ha'.1 v hv)
    have hnonempty := (mem_filter.mp hnew).2
    have hlo := two_le_boundary_card M hbridge _ hnonempty
    have hsub : boundaryDarts M (residualComponent M {v} a) ⊆ boundaryDarts M U := by
      intro e he
      have hea := (mem_filter.mp he).2.1
      have hec := (mem_residualComponent M {v} a _).mp hea
      have heu := (hpath _ _ hec.2.2).mp ha
      have hev := residual_boundary_ends_in_removed M {v} a he
      have hev' : M.atom (M.mate e) = v := by simpa only [mem_singleton] using hev
      exact mem_filter.mpr ⟨mem_univ _,heu,hev'.symm ▸ hvnot⟩
    apply Finset.eq_of_subset_of_card_le hsub
    omega
  intro a ha b hb
  have hba := hboundary a ha
  have hbb := hboundary b hb
  obtain ⟨e,he⟩ := card_pos.mp (by omega : 0 < (boundaryDarts M U).card)
  have hea : M.atom e ∈ residualComponent M {v} a := by
    have hh := he
    rw [← hba] at hh
    exact (mem_filter.mp hh).2.1
  have heb : M.atom e ∈ residualComponent M {v} b := by
    have hh := he
    rw [← hbb] at hh
    exact (mem_filter.mp hh).2.1
  have hab := residualComponent_eq_of_mem M {v} hea heb
  have hb' := mem_sdiff.mp (hU hb)
  have hbself : b ∈ residualComponent M {v} b := (mem_residualComponent M {v} b b).mpr
    ⟨hb'.1,hb'.2,Relation.EqvGen.refl b⟩
  rw [← hab] at hbself
  exact (eraseAtoms_sameComponent_iff M {v} a b).mpr ((mem_residualComponent M {v} a b).mp hbself).2.2

/-- Removing all old boundary endpoints makes the retained side closed. -/
theorem boundary_erase_eq_empty_of_old_boundary_ends_removed (M : Molecule V D)
    (Y U : Finset V) (hend : ∀ e ∈ boundaryDarts M U, M.atom (M.mate e) ∈ Y) :
    boundaryDarts (eraseAtoms M Y) U = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  have hmem := (mem_filter.mp he).2
  have hold : e.val ∈ boundaryDarts M U := mem_filter.mpr ⟨mem_univ _,hmem⟩
  exact e.property.2 (hend e.val hold)

/-- The retained two-bond side is connected in its literal OLD induced
carrier, the form used for the next preliminary source input. -/
theorem two_boundary_side_induced_connected (M : Molecule V D)
    (hbridge : ∀ e, ¬ IsBridge M e)
    (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b)
    {v : V} (hv : v ∈ M.atoms) (U : Finset V) (hU : U ⊆ M.atoms \ {v})
    (hcard : (boundaryDarts M U).card = 2)
    (hend : ∀ e ∈ boundaryDarts M U, M.atom (M.mate e) = v) :
    ∀ a ∈ U, ∀ b ∈ U, (Mole.induced M U).SameComponent a b := by
  have hclosed : boundaryDarts (eraseAtoms M {v}) U = ∅ :=
    boundary_erase_eq_empty_of_old_boundary_ends_removed M {v} U
      (fun e he => by simpa only [mem_singleton] using hend e he)
  intro a ha b hb
  have hp := two_boundary_side_connected_after_erase M hbridge hconn hv U hU hcard hend a ha b hb
  have hpi := sameComponent_induced_of_boundary_empty (eraseAtoms M {v}) U hclosed ha hp
  apply Relation.EqvGen.mono (fun c d hcd => ?_) _ _ hpi
  obtain ⟨e,hec,hed⟩ := hcd
  exact ⟨⟨e.val.val,e.property⟩,hec,hed⟩

end WaveTurbulence.MoleProp
