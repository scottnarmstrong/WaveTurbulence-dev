/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103LocalRemoval
import Mathlib.Tactic

/-! # Source good-case rank loss by commuting incident B and R operations -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- An edge incident to the removed atom was already absent after R. -/
def eraseIncidentBondDartEquiv (M : Molecule V D) {v : V} {e : D} (he : M.atom e = v) :
    RetainedDart (eraseBond M e) {v} ≃ RetainedDart M {v} where
  toFun z := ⟨z.val.val,z.property⟩
  invFun z := by
    have hne : z.val ≠ e := by
      intro h
      exact z.property.1 (by simpa only [mem_singleton,h,he])
    have hnme : z.val ≠ M.mate e := by
      intro h
      exact z.property.2 (by simpa only [mem_singleton,h,M.mate_mate,he])
    exact ⟨⟨z.val,hne,hnme⟩,z.property⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

/-- Actual B and R commute at the incident atom, on actual circuit ranks. -/
theorem circuitRank_eraseIncidentBond_then_atom (M : Molecule V D) {v : V} {e : D}
    (he : M.atom e = v) :
    (eraseAtoms (eraseBond M e) {v}).circuitRank = (eraseAtoms M {v}).circuitRank :=
  circuitRank_eq_of_dart_equiv _ _ (eraseIncidentBondDartEquiv M he) rfl
    (fun _ => rfl) (fun _ => Subtype.ext rfl) (fun _ => rfl)

/-- A loopless incident bond contributes exactly one dart at this vertex. -/
theorem degree_eraseIncidentBond_add_one (M : Molecule V D)
    (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) {v : V} {e : D} (he : M.atom e = v) :
    (eraseBond M e).deg v + 1 = M.deg v := by
  classical
  have hm : M.atom (M.mate e) ≠ v := fun h => hloop e (he.trans h.symm)
  have hc : (eraseBond M e).deg v = ((M.dartsAt v).erase e).card := by
    apply card_bij (fun z _ => z.val)
    · intro z hz
      exact mem_erase.mpr ⟨z.property.1,(Mole.mem_dartsAt M v _).mpr ((Mole.mem_dartsAt _ v z).mp hz)⟩
    · intro z _ w _ h
      exact Subtype.ext h
    · intro z hz
      have hh := mem_erase.mp hz
      have hzv := (Mole.mem_dartsAt M v z).mp hh.2
      have hzme : z ≠ M.mate e := fun h => hm (h ▸ hzv)
      exact ⟨⟨z,hh.1,hzme⟩,(Mole.mem_dartsAt _ v _).mpr hzv,rfl⟩
  rw [hc]
  exact card_erase_add_one ((Mole.mem_dartsAt M v e).mpr he)

/-- Source case (1), degree three with exactly one incident bridge: B
reduces it to the local degree-two case, so the actual loss is one circuit. -/
theorem circuitRank_erase_three_one_incident_bridge (M : Molecule V D)
    [DecidablePred (IsBridge M)]
    (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) {v : V} (hv : v ∈ M.atoms)
    (hv3 : M.deg v = 3) (hcount : ((M.dartsAt v).filter (IsBridge M)).card = 1) :
    (eraseAtoms M {v}).circuitRank = M.circuitRank - 1 := by
  classical
  obtain ⟨e,he⟩ := card_eq_one.mp hcount
  have hem : e ∈ (M.dartsAt v).filter (IsBridge M) := by rw [he]; simp
  have hev := (Mole.mem_dartsAt M v e).mp (mem_filter.mp hem).1
  have heb := (mem_filter.mp hem).2
  have hdeg := degree_eraseIncidentBond_add_one M hloop hev
  have hnb : ∀ z, (eraseBond M e).atom z = v → ¬ IsBridge (eraseBond M e) z := by
    intro z hz hb
    have hold : IsBridge M z.val := (isBridge_eraseBond_iff M e heb z).mp hb
    have hzm : z.val ∈ (M.dartsAt v).filter (IsBridge M) :=
      mem_filter.mpr ⟨(Mole.mem_dartsAt M v z.val).mpr hz,hold⟩
    rw [he] at hzm
    exact z.property.1 (mem_singleton.mp hzm)
  have hloop' : ∀ z, (eraseBond M e).atom z ≠ (eraseBond M e).atom ((eraseBond M e).mate z) :=
    fun z => hloop z.val
  have hR := circuitRank_erase_two_of_no_incident_bridges (eraseBond M e) hloop' hv (by omega) hnb
  rw [circuitRank_eraseIncidentBond_then_atom M hev,circuitRank_eraseBond_eq M e heb] at hR
  exact hR

/-- Deleting an incident bridge removes just that bridge from the local
bridge count; every other surviving bridge status is unchanged. -/
theorem incident_bridge_count_erase_add_one (M : Molecule V D)
    [DecidablePred (IsBridge M)] (e : D) [DecidablePred (IsBridge (eraseBond M e))]
    (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) {v : V}
    (hev : M.atom e = v) (heb : IsBridge M e) :
    (((eraseBond M e).dartsAt v).filter (IsBridge (eraseBond M e))).card + 1 =
      ((M.dartsAt v).filter (IsBridge M)).card := by
  classical
  have hm : M.atom (M.mate e) ≠ v := fun h => hloop e (hev.trans h.symm)
  have hc : (((eraseBond M e).dartsAt v).filter (IsBridge (eraseBond M e))).card =
      (((M.dartsAt v).filter (IsBridge M)).erase e).card := by
    apply card_bij (fun z _ => z.val)
    · intro z hz
      have hh := mem_filter.mp hz
      exact mem_erase.mpr ⟨z.property.1,mem_filter.mpr
        ⟨(Mole.mem_dartsAt M v z.val).mpr ((Mole.mem_dartsAt _ v z).mp hh.1),
          (isBridge_eraseBond_iff M e heb z).mp hh.2⟩⟩
    · intro z _ w _ h
      exact Subtype.ext h
    · intro z hz
      have hh := mem_erase.mp hz
      have hzv := (Mole.mem_dartsAt M v z).mp (mem_filter.mp hh.2).1
      have hzme : z ≠ M.mate e := fun h => hm (h ▸ hzv)
      let z' : WithoutBondDart M e := ⟨z,hh.1,hzme⟩
      refine ⟨z',mem_filter.mpr ⟨(Mole.mem_dartsAt _ v z').mpr hzv,?_⟩,rfl⟩
      exact (isBridge_eraseBond_iff M e heb z').mpr (mem_filter.mp hh.2).2
  rw [hc]
  exact card_erase_add_one (mem_filter.mpr ⟨(Mole.mem_dartsAt M v e).mpr hev,heb⟩)

/-- Source case (3): two incident bridges at a degree-four atom leave the
local degree-three/one-bridge case after B, hence actual circuit loss one. -/
theorem circuitRank_erase_four_two_incident_bridges (M : Molecule V D)
    [DecidablePred (IsBridge M)]
    (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) {v : V} (hv : v ∈ M.atoms)
    (hv4 : M.deg v = 4) (hcount : ((M.dartsAt v).filter (IsBridge M)).card = 2) :
    (eraseAtoms M {v}).circuitRank = M.circuitRank - 1 := by
  classical
  obtain ⟨e,he⟩ := card_pos.mp (by omega : 0 < ((M.dartsAt v).filter (IsBridge M)).card)
  have hev := (Mole.mem_dartsAt M v e).mp (mem_filter.mp he).1
  have heb := (mem_filter.mp he).2
  have hdeg := degree_eraseIncidentBond_add_one M hloop hev
  have hbcount := incident_bridge_count_erase_add_one M e hloop hev heb
  have hloop' : ∀ z, (eraseBond M e).atom z ≠ (eraseBond M e).atom ((eraseBond M e).mate z) :=
    fun z => hloop z.val
  have hR := circuitRank_erase_three_one_incident_bridge (eraseBond M e) hloop' hv
    (by omega) (by omega)
  rw [circuitRank_eraseIncidentBond_then_atom M hev,circuitRank_eraseBond_eq M e heb] at hR
  exact hR

end WaveTurbulence.MoleProp
