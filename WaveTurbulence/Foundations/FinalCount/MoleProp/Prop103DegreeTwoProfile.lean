/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103BridgeProfile
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103LocalRemoval
public import WaveTurbulence.Foundations.FinalCount.MoleProp.SimpleErasure
public import WaveTurbulence.Foundations.FinalCount.MoleProp.SimpleGraphRank
import Mathlib.Tactic

/-! # The actual preliminary degree-two removal restores the initial profile -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A simple connected single-degree-two/four graph has no bridges, and
its actual degree-two R deletion yields the original two-degree-three
profile, with actual connectivity, molecule axioms, and circuit loss one. -/
theorem erase_one_two_restores_initial_profile (M : Molecule V D) (hM : M.IsMolecule)
    (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z))
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1)
    (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b)
    (hprof : OneTwoProfile M) :
    ∃ v ∈ M.atoms, M.deg v = 2 ∧ (eraseAtoms M {v}).IsMolecule ∧
      TwoThreeProfile (eraseAtoms M {v}) ∧
      (∀ a ∈ (eraseAtoms M {v}).atoms, ∀ b ∈ (eraseAtoms M {v}).atoms,
        (eraseAtoms M {v}).SameComponent a b) ∧
      (eraseAtoms M {v}).circuitRank = M.circuitRank - 1 ∧
      (eraseAtoms M {v}).atoms.card < M.atoms.card := by
  classical
  obtain ⟨v,hv,hv2,hrest⟩ := hprof
  have hEven : ∀ a ∈ M.atoms, Even (M.deg a) := by
    intro a ha
    by_cases hav : a = v
    · exact hav.symm ▸ (hv2.symm ▸ (by decide : Even (2 : ℕ)))
    · rw [hrest a ha hav]
      decide
  have hbridge := bridgeless_of_even_degrees M hEven
  obtain ⟨x,y,hxy,hstar⟩ := card_eq_two.mp hv2
  have hx : M.atom x = v := (Mole.mem_dartsAt M v x).mp (by rw [hstar]; simp)
  have hy : M.atom y = v := (Mole.mem_dartsAt M v y).mp (by rw [hstar]; simp)
  let p := M.atom (M.mate x)
  let q := M.atom (M.mate y)
  have hpv : p ≠ v := fun h => hloop x (hx.trans h.symm)
  have hqv : q ≠ v := fun h => hloop y (hy.trans h.symm)
  have hpq : p ≠ q := by
    intro h
    apply hxy
    exact otherEndpoint_injOn_dartsAt M hloop hsimple v
      ((Mole.mem_dartsAt M v x).mpr hx) ((Mole.mem_dartsAt M v y).mpr hy) h
  have hpM : p ∈ M.atoms := M.atom_mem _
  have hqM : q ∈ M.atoms := M.atom_mem _
  have hpN : p ∈ (eraseAtoms M {v}).atoms := mem_sdiff.mpr ⟨hpM,by simpa only [mem_singleton] using hpv⟩
  have hqN : q ∈ (eraseAtoms M {v}).atoms := mem_sdiff.mpr ⟨hqM,by simpa only [mem_singleton] using hqv⟩
  have hremoved (a : V) : removedDartsAt M {v} a = neighborDarts M a v := by
    ext z
    simp only [removedDartsAt,neighborDarts,mem_filter,mem_singleton]
  have hneighborP : (neighborDarts M p v).card = 1 := by
    have hlo : 0 < (neighborDarts M p v).card := card_pos.mpr
      ⟨M.mate x,mem_filter.mpr ⟨(Mole.mem_dartsAt M p _).mpr rfl,by rw [M.mate_mate,hx]⟩⟩
    have hhi : (neighborDarts M p v).card ≤ 1 := by rw [card_neighborDarts M hpv]; exact hsimple _ _ hpv
    omega
  have hneighborQ : (neighborDarts M q v).card = 1 := by
    have hlo : 0 < (neighborDarts M q v).card := card_pos.mpr
      ⟨M.mate y,mem_filter.mpr ⟨(Mole.mem_dartsAt M q _).mpr rfl,by rw [M.mate_mate,hy]⟩⟩
    have hhi : (neighborDarts M q v).card ≤ 1 := by rw [card_neighborDarts M hqv]; exact hsimple _ _ hqv
    omega
  have hpdeg := deg_eraseAtoms_add_removed M {v} (by simpa only [mem_singleton] using hpv)
  have hqdeg := deg_eraseAtoms_add_removed M {v} (by simpa only [mem_singleton] using hqv)
  rw [hremoved,hneighborP,hrest p hpM hpv] at hpdeg
  rw [hremoved,hneighborQ,hrest q hqM hqv] at hqdeg
  have hprofile : TwoThreeProfile (eraseAtoms M {v}) := by
    refine ⟨p,hpN,q,hqN,hpq,by omega,by omega,?_⟩
    intro a ha hap haq
    have ha' := mem_sdiff.mp ha
    have hav : a ≠ v := by simpa only [mem_singleton] using ha'.2
    have he : removedDartsAt M {v} a = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      have hza := (Mole.mem_dartsAt M a z).mp (mem_filter.mp hz).1
      have hzm : M.atom (M.mate z) = v := by simpa only [mem_singleton] using (mem_filter.mp hz).2
      have hmstar : M.mate z ∈ M.dartsAt v := (Mole.mem_dartsAt M v _).mpr hzm
      rw [hstar] at hmstar
      simp only [mem_insert,mem_singleton] at hmstar
      rcases hmstar with h | h
      · have hz' : z = M.mate x := by simpa only [M.mate_mate] using congrArg M.mate h
        exact hap (hza.symm.trans (congrArg M.atom hz'))
      · have hz' : z = M.mate y := by simpa only [M.mate_mate] using congrArg M.mate h
        exact haq (hza.symm.trans (congrArg M.atom hz'))
    have hh := deg_eraseAtoms_add_removed M {v} ha'.2
    rw [he,card_empty,hrest a ha'.1 hav] at hh
    omega
  have hlt : (eraseAtoms M {v}).atoms.card < M.atoms.card := by
    apply card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset,?_⟩
    intro h
    have hh : v ∈ (eraseAtoms M {v}).atoms := h.symm ▸ hv
    exact (mem_sdiff.mp hh).2 (mem_singleton_self v)
  exact ⟨v,hv,hv2,isMolecule_eraseAtoms M hM {v},hprofile,
    erase_low_degree_connected M hbridge hconn hv (by omega),
    circuitRank_erase_two_of_bridgeless M hloop hbridge hv hv2,hlt⟩

end WaveTurbulence.MoleProp
