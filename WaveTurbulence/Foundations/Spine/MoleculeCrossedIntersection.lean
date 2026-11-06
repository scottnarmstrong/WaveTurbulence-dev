/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.MoleculeFullIntersections
public import WaveTurbulence.Foundations.Spine.MoleculeOrientationUnion
import WaveTurbulence.Foundations.Spine.SourceIntersectionConnectivity
import Mathlib.Tactic

/-!
# Intersection blocks and exterior pieces in the crossed-joint case

DH23 Lemma 4.11(2): once each group has one joint inside and one outside
the other, their intersection is the middle block of the concatenation.
-/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D)

/-- The actual intersection block has as joints the two crossed interior
joints, with exactly one incidence of each orientation at each. -/
theorem crossed_intersection_isBlock (hM : M.IsMolecule) {A B : Finset V} {a1 a2 b1 b2 : V}
    (hA : M.IsBlock A a1 a2) (hB : M.IsBlock B b1 b2)
    (ha1B : a1 ∈ B) (ha11 : a1 ≠ b1) (ha12 : a1 ≠ b2)
    (hb1A : b1 ∈ A) (hb11 : b1 ≠ a1) (hb12 : b1 ≠ a2)
    (ha2out : a2 ∉ B) (hb2out : b2 ∉ A) : M.IsBlock (A ∩ B) a1 b1 := by
  have hfulla := hB.2.2.2.2.2.2.2.2.1 a1 ha1B ha11 ha12
  have hfullb := hA.2.2.2.2.2.2.2.2.1 b1 hb1A hb11 hb12
  have ho1 : M.outIn (A ∩ B) a1 = M.outIn A a1 :=
    orientedIn_inter_eq_of_full_degree M hM (hB.1 ha1B) hfulla A true
  have hi1 : M.inIn (A ∩ B) a1 = M.inIn A a1 :=
    orientedIn_inter_eq_of_full_degree M hM (hB.1 ha1B) hfulla A false
  have ho2 : M.outIn (A ∩ B) b1 = M.outIn B b1 := by
    rw [Finset.inter_comm]
    exact orientedIn_inter_eq_of_full_degree M hM (hA.1 hb1A) hfullb B true
  have hi2 : M.inIn (A ∩ B) b1 = M.inIn B b1 := by
    rw [Finset.inter_comm]
    exact orientedIn_inter_eq_of_full_degree M hM (hA.1 hb1A) hfullb B false
  refine ⟨fun _ hz => hA.1 (Finset.mem_inter.mp hz).1,
    Finset.mem_inter.mpr ⟨hA.2.1,ha1B⟩,Finset.mem_inter.mpr ⟨hb1A,hB.2.1⟩,ha11,
    ho1.trans hA.2.2.2.2.1,hi1.trans hA.2.2.2.2.2.1,
    ho2.trans hB.2.2.2.2.1,hi2.trans hB.2.2.2.2.2.1,?_,
    LGSpine.source_groupConnected_inter_of_one_joint M hM hA.2.2.2.2.2.2.2.2.2 hB hb2out⟩
  intro z hz hza hzb
  obtain ⟨hzA,hzB⟩ := Finset.mem_inter.mp hz
  have hza2 : z ≠ a2 := fun he => ha2out (he ▸ hzB)
  have hzb2 : z ≠ b2 := fun he => hb2out (he ▸ hzA)
  have hdA := hA.2.2.2.2.2.2.2.2.1 z hzA hza hza2
  have hdB := hB.2.2.2.2.2.2.2.2.1 z hzB hzb hzb2
  change ((M.dartsAt z).filter (M.InGroup (A ∩ B))).card = 4
  rw [internal_inter_eq_of_full_degree M hM (hB.1 hzB) hdB A]
  exact hdA

/-- At an atom outside B, every incidence in A remains in the exterior
piece with b1 adjoined, since the other joint b2 is outside A. -/
theorem left_piece_internal_eq (hM : M.IsMolecule) {A B : Finset V} {b1 b2 v : V}
    (hB : M.IsBlock B b1 b2) (hb1A : b1 ∈ A) (hb2out : b2 ∉ A) (hv : v ∈ A \ B) :
    (M.dartsAt v).filter (M.InGroup ((A \ B) ∪ {b1})) = (M.dartsAt v).filter (M.InGroup A) := by
  have hsub : (A \ B) ∪ {b1} ⊆ A := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzP | hzB
    · exact (Finset.mem_sdiff.mp hzP).1
    · exact (Finset.mem_singleton.mp hzB).symm ▸ hb1A
  have hvA := (Finset.mem_sdiff.mp hv).1
  have hvB := (Finset.mem_sdiff.mp hv).2
  ext x
  constructor
  · intro hx
    obtain ⟨hxv,hxa,hxm⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hxv,hsub hxa,hsub hxm⟩
  · intro hx
    obtain ⟨hxv,hxa,hxmA⟩ := Finset.mem_filter.mp hx
    have hxv' := (mem_dartsAt M v x).mp hxv
    have hmC : M.atom (M.mate x) ∈ (A \ B) ∪ {b1} := by
      by_cases hmB : M.atom (M.mate x) ∈ B
      · have hadj : M.Adj v (M.atom (M.mate x)) := ⟨x,hxv',rfl⟩
        rcases block_entry_is_joint M hM hB hvB hmB hadj with hm1 | hm2
        · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hm1)
        · exact (hb2out (hm2 ▸ hxmA)).elim
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxmA,hmB⟩)
    exact Finset.mem_filter.mpr ⟨hxv,hxv'.symm ▸ Finset.mem_union_left _ hv,hmC⟩

/-- Any exact internal-incidence identity preserves each orientation count. -/
theorem orientedIn_eq_of_internal_eq {A B : Finset V} {v : V}
    (he : (M.dartsAt v).filter (M.InGroup A) = (M.dartsAt v).filter (M.InGroup B)) (b : Bool) :
    ((M.dartsAt v).filter (fun x => M.InGroup A x ∧ M.out x = b)).card =
      ((M.dartsAt v).filter (fun x => M.InGroup B x ∧ M.out x = b)).card := by
  simp only [← Finset.filter_filter]
  rw [he]

end WaveTurbulence.Mole
