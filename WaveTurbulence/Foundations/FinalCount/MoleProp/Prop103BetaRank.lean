/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103BetaComplement
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103CutConnectivity
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103LocalRemoval
import Mathlib.Tactic

/-! # Actual two-circuit loss at a permitted beta joint -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A permitted beta joint has exactly two newly bounded components when
removed, hence loses exactly two circuits. All components and stars are
constructed from the actual graph and split. -/
theorem circuitRank_erase_beta_joint (M : Molecule V D) (hM : M.IsMolecule)
    (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) {v : V} {x y : D}
    (hd : (withFreshAtom M).IsCutData (some v) none x y) (hv4 : M.deg v = 4)
    (hnb : ∀ e, M.atom e = v → ¬ IsBridge M e)
    (hdisc : ¬ ((withFreshAtom M).cut (some v) none x y).SameComponent (some v) none) :
    (eraseAtoms M {v}).circuitRank = M.circuitRank - 2 := by
  classical
  have hv : v ∈ M.atoms := by
    obtain ⟨a,ha,hav⟩ := mem_map.mp hd.1
    change some a = some v at hav
    exact Option.some.inj hav ▸ ha
  have hx : M.atom x = v := Option.some.inj hd.2.2.1
  have hy : M.atom y = v := Option.some.inj hd.2.2.2.1
  obtain ⟨r,s,hr,hs,hro,hso,hxy,hxr,hxs,hyr,hys,hrs,hstar⟩ :=
    exists_remaining_mixed_pair M hM hv hv4 hx hy hd.2.2.2.2.2.1 hd.2.2.2.2.2.2
  obtain ⟨U,hU,hboundary,hxm,hym⟩ := exists_old_cut_of_beta_split M hloop hx hy hdisc
  let T := (M.atoms \ {v}) \ U
  have hTboundary := beta_other_side_boundary M hloop hx hy hr hs hxr hxs hyr hys hstar U hU hboundary
  have hrT : M.atom (M.mate r) ∈ T := by
    have hh : M.mate r ∈ boundaryDarts M T := by rw [hTboundary]; simp
    exact (mem_filter.mp hh).2.1
  have hxu := mem_sdiff.mp (hU hxm)
  have hru := mem_sdiff.mp (mem_sdiff.mp hrT).1
  have hxv : M.atom (M.mate x) ≠ v := by simpa only [mem_singleton] using hxu.2
  have hrv : M.atom (M.mate r) ≠ v := by simpa only [mem_singleton] using hru.2
  have hXPath : M.SameComponent (M.atom (M.mate x)) v :=
    Relation.EqvGen.rel _ _ ⟨M.mate x,rfl,by rw [M.mate_mate,hx]⟩
  have hRPath : M.SameComponent (M.atom (M.mate r)) v :=
    Relation.EqvGen.rel _ _ ⟨M.mate r,rfl,by rw [M.mate_mate,hr]⟩
  have hXnew := residualComponent_mem_newComponents_of_sameComponent M hv hxu.1 hxv hXPath
  have hRnew := residualComponent_mem_newComponents_of_sameComponent M hv hru.1 hrv hRPath
  have hclosed : boundaryDarts (eraseAtoms M {v}) U = ∅ := by
    apply boundary_erase_eq_empty_of_old_boundary_ends_removed
    intro e he
    rw [hboundary] at he
    simp only [mem_insert,mem_singleton] at he
    rcases he with rfl | rfl
    · simpa only [M.mate_mate,hx,mem_singleton]
    · simpa only [M.mate_mate,hy,mem_singleton]
  have hne : residualComponent M {v} (M.atom (M.mate x)) ≠
      residualComponent M {v} (M.atom (M.mate r)) := by
    intro heq
    have hrself : M.atom (M.mate r) ∈ residualComponent M {v} (M.atom (M.mate r)) :=
      (mem_residualComponent M {v} _ _).mpr ⟨hru.1,hru.2,Relation.EqvGen.refl _⟩
    rw [← heq] at hrself
    have hp := (eraseAtoms_sameComponent_iff M {v} _ _).mpr ((mem_residualComponent M {v} _ _).mp hrself).2.2
    have hruU := (sameComponent_mem_iff_of_boundary_empty (eraseAtoms M {v}) U hclosed hp).mp hxm
    exact (mem_sdiff.mp hrT).2 hruU
  have hlo : 2 ≤ (newComponents M {v}).card := by
    have hs' : {residualComponent M {v} (M.atom (M.mate x)),residualComponent M {v} (M.atom (M.mate r))} ⊆
        newComponents M {v} := by
      simp only [insert_subset_iff,singleton_subset_iff]
      exact ⟨hXnew,hRnew⟩
    have hh := card_le_card hs'
    rwa [card_pair hne] at hh
  have hhi := two_mul_newComponents_le_of_no_incident_bridges M v hnb
  have hc : (newComponents M {v}).card = 2 := by omega
  have hi := incident_card_eq_deg_of_loopless M hloop v
  have hχ := circuitRank_erase_singleton_sub_general M hv
  rw [hc,hi,hv4] at hχ
  omega

end WaveTurbulence.MoleProp
