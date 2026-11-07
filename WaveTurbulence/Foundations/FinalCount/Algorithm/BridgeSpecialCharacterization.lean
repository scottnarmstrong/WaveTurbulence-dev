/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.BridgeStructure
public import WaveTurbulence.Foundations.FinalCount.Algorithm.BridgeSimpleDegreeTwo
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DegreeTwoDoubleAlternative
public import WaveTurbulence.Foundations.FinalCount.Degen.LadderDeletionGeometry
import Mathlib.Tactic

/-! # A BR333 step preserves V2-star exactly for source special bridges -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem eraseBond_pair_of_remote_other (M : Molecule V D) (e : D) {b : V}
    (ha : M.atom e ≠ b) (hb : M.atom (M.mate e) ≠ b) (a : V) :
    (eraseBond M e).bondsBetween a b = M.bondsBetween a b := by
  rw [bondsBetween_symm (eraseBond M e) a b,
    eraseBond_bondsBetween_of_not_endpoint M e ha hb,bondsBetween_symm M b a]

theorem bridge333_post_degrees (M : Molecule V D) (e : D) (hb : Degen.IsBridge M e)
    (h1 : M.deg (M.atom e) = 3) (h2 : M.deg (M.atom (M.mate e)) = 3) :
    (eraseBond M e).deg (M.atom e) = 2 ∧ (eraseBond M e).deg (M.atom (M.mate e)) = 2 := by
  have hne := appb_bridge_endpoints_distinct M e hb
  have ha := appb_eraseBond_degree M e (M.atom e)
  have hc := appb_eraseBond_degree M e (M.atom (M.mate e))
  simp only [hne,Ne.symm hne,ite_true,ite_false,add_zero] at ha hc
  omega

/-- Source BR333 equality characterization, with the bridge represented
by its outgoing dart as required by AppbSpecial. -/
theorem bridge333_special_iff_post_nonsimple (M : Molecule V D) (hno : AppbNoLoops M)
    (e : D) (hb : Degen.IsBridge M e) (hout : M.out e = true)
    (h1 : M.deg (M.atom e) = 3) (h2 : M.deg (M.atom (M.mate e)) = 3) :
    AppbSpecial M e ↔
      ¬SimpleDegreeTwo (eraseBond M e) (M.atom e) ∧
      ¬SimpleDegreeTwo (eraseBond M e) (M.atom (M.mate e)) := by
  have hd := bridge333_post_degrees M e hb h1 h2
  constructor
  · rintro ⟨_,_,_,c,hc,d,hd',hcd,hca,hcb,hda,hdb,_,hac,hbd⟩
    have hac' : (eraseBond M e).bondsBetween (M.atom e) c = 2 :=
      (eraseBond_pair_of_remote_other M e hca.symm hcb.symm _).trans hac
    have hbd' : (eraseBond M e).bondsBetween (M.atom (M.mate e)) d = 2 :=
      (eraseBond_pair_of_remote_other M e hda.symm hdb.symm _).trans hbd
    exact ⟨not_simpleDegreeTwo_of_double _ hca.symm hd.1 hac',
      not_simpleDegreeTwo_of_double _ hdb.symm hd.2 hbd'⟩
  · rintro ⟨hn1,hn2⟩
    have hno' : AppbNoLoops (eraseBond M e) := fun x => hno x.val
    obtain ⟨c,hc,hca,hac⟩ := (degree_two_not_simple_iff_double (eraseBond M e) hno'
      (M.atom_mem e) hd.1).mp hn1
    obtain ⟨d,hd',hdb,hbd⟩ := (degree_two_not_simple_iff_double (eraseBond M e) hno'
      (M.atom_mem (M.mate e)) hd.2).mp hn2
    have hpac : (eraseBond M e).SameComponent (M.atom e) c :=
      Relation.EqvGen.rel _ _ (Degen.adj_of_bondsBetween_pos _ hca.symm (by rw [hac]; decide))
    have hpbd : (eraseBond M e).SameComponent (M.atom (M.mate e)) d :=
      Relation.EqvGen.rel _ _ (Degen.adj_of_bondsBetween_pos _ hdb.symm (by rw [hbd]; decide))
    have hcb : c ≠ M.atom (M.mate e) := by
      intro he
      exact bridge_endpoints_not_post_connected M e hb (he ▸ hpac)
    have hda : d ≠ M.atom e := by
      intro he
      exact bridge_endpoints_not_post_connected M e hb ((he ▸ hpbd).symm)
    have hcd : c ≠ d := by
      intro he
      have hp : (eraseBond M e).SameComponent c (M.atom (M.mate e)) := by
        rw [he]; exact hpbd.symm
      exact bridge_endpoints_not_post_connected M e hb (Relation.EqvGen.trans _ _ _ hpac hp)
    have hac' : M.bondsBetween (M.atom e) c = 2 :=
      (eraseBond_pair_of_remote_other M e hca.symm hcb.symm _).symm.trans hac
    have hbd' : M.bondsBetween (M.atom (M.mate e)) d = 2 :=
      (eraseBond_pair_of_remote_other M e hda.symm hdb.symm _).symm.trans hbd
    exact ⟨hout,h1,h2,c,hc,d,hd',hcd,hca,hcb,hda,hdb,
      bridge_multiplicity_eq_one M e hb,hac',hbd'⟩

/-- DH23's BR333 V2-star increment is zero exactly when the removed
bridge was special. This supplies the actual graph predicate behind z1. -/
theorem bridge333_simpleDegreeTwo_eq_iff_special (M : Molecule V D) (hno : AppbNoLoops M)
    (e : D) (hb : Degen.IsBridge M e) (hout : M.out e = true)
    (h1 : M.deg (M.atom e) = 3) (h2 : M.deg (M.atom (M.mate e)) = 3) :
    (simpleDegreeTwoAtoms (eraseBond M e)).card = (simpleDegreeTwoAtoms M).card ↔ AppbSpecial M e :=
  (bridge333_simpleDegreeTwo_eq_iff M e hb h1 h2).trans
    (bridge333_special_iff_post_nonsimple M hno e hb hout h1 h2).symm

end WaveTurbulence.Mole.AppbAlgorithm
