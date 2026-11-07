/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBBridgeComponents
public import WaveTurbulence.Foundations.FinalCount.AppBDegreeCountTransport
import Mathlib.Tactic

/-! # DH23 BR-N: circuit rank and the exact degree-three change -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_bridge_endpoints_distinct (M : Molecule V D) (e : D) (hb : Degen.IsBridge M e) :
    M.atom e ≠ M.atom (M.mate e) := by
  intro he
  apply hb
  rw [he]
  exact Relation.EqvGen.refl _

theorem appb_bridge_circuitRank (M : Molecule V D) (e : D) (hb : Degen.IsBridge M e) :
    (eraseBond M e).circuitRank = M.circuitRank := by
  have he := appb_eraseBond_card_bonds M e
  have hf := appb_bridge_numComponents M e hb
  unfold Molecule.circuitRank
  change ((eraseBond M e).bonds.card : ℤ)-M.atoms.card+(eraseBond M e).numComponents = _
  omega

theorem appb_bridge_degreeThree (M : Molecule V D) (e : D) (hb : Degen.IsBridge M e) :
    ((appbDegreeAtoms (eraseBond M e) 3).card : ℤ)-(appbDegreeAtoms M 3).card =
      ((if M.deg (M.atom e) = 4 then 1 else 0)-(if M.deg (M.atom e) = 3 then 1 else 0))+
      ((if M.deg (M.atom (M.mate e)) = 4 then 1 else 0)-
        (if M.deg (M.atom (M.mate e)) = 3 then 1 else 0)) := by
  have hne := appb_bridge_endpoints_distinct M e hb
  have hA := appb_eraseBond_degree M e (M.atom e)
  have hB := appb_eraseBond_degree M e (M.atom (M.mate e))
  simp only [ite_true,hne,Ne.symm hne,ite_false,add_zero] at hA hB
  have hdeg : ∀ v ∈ M.atoms,v ∉ ({M.atom e,M.atom (M.mate e)} : Finset V) →
      (eraseBond M e).deg v = M.deg v := by
    intro v hv hn
    have ha : M.atom e ≠ v := by intro he; apply hn; simp [← he]
    have hb : M.atom (M.mate e) ≠ v := by intro he; apply hn; simp [← he]
    have hh := appb_eraseBond_degree M e v
    simpa only [ha,hb,ite_false,add_zero] using hh
  rw [appb_degreeCount_difference_of_local_change M (eraseBond M e) rfl
    {M.atom e,M.atom (M.mate e)} (by intro a ha; simp only [mem_insert,mem_singleton] at ha; rcases ha with rfl | rfl <;> exact M.atom_mem _) hdeg 3,
    sum_pair hne]
  have ha : (eraseBond M e).deg (M.atom e) = 3 ↔ M.deg (M.atom e) = 4 := by omega
  have hb : (eraseBond M e).deg (M.atom (M.mate e)) = 3 ↔ M.deg (M.atom (M.mate e)) = 4 := by omega
  simp only [ha,hb]

/-- DH23 brprop: Delta V3 >= -2, with equality exactly at two degree-three
endpoints. The corrected Delta nu=-2 is appb_bridge_nu. -/
theorem appb_bridge_degreeThree_lower_eq (M : Molecule V D) (e : D) (hb : Degen.IsBridge M e) :
    -2 ≤ ((appbDegreeAtoms (eraseBond M e) 3).card : ℤ)-(appbDegreeAtoms M 3).card ∧
    (((appbDegreeAtoms (eraseBond M e) 3).card : ℤ)-(appbDegreeAtoms M 3).card = -2 ↔
      M.deg (M.atom e) = 3 ∧ M.deg (M.atom (M.mate e)) = 3) := by
  rw [appb_bridge_degreeThree M e hb]
  by_cases ha3 : M.deg (M.atom e) = 3 <;> by_cases ha4 : M.deg (M.atom e) = 4 <;>
    by_cases hb3 : M.deg (M.atom (M.mate e)) = 3 <;>
    by_cases hb4 : M.deg (M.atom (M.mate e)) = 4 <;> simp_all

end WaveTurbulence.Mole
