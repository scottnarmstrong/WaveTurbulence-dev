/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeBlockConcatenation
public import WaveTurbulence.Foundations.Molecule.MoleculeOrientationGroups
import WaveTurbulence.Foundations.Molecule.SourceGroupConnectivity
import WaveTurbulence.Foundations.Molecule.VineLocalDartObjects
import WaveTurbulence.Foundations.Molecule.VineLocalDartErasure
import Mathlib.Tactic

/-!
# Actual block/hyper-block realization of concatenation

TARGET `defblock` and DH23 Lemma 4.11(b), under the explicit connected-block
convention. The hyper-block witness is an actual joint-to-joint bond whose
deletion leaves a block on the union atom set.
-/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

/-- Two connected blocks sharing exactly one joint concatenate to an actual
block or hyper-block, according to whether the other joints are bonded. -/
theorem blocks_concatenate (hM : M.IsMolecule) {A B : Finset V} {a b c : V}
    (hA : M.IsBlock A a c) (hB : M.IsBlock B b c) (hcA : GroupConnected M A)
    (hi : A ∩ B = {c}) : M.IsBlock (A ∪ B) a b ∨ IsHyperBlock M (A ∪ B) a b := by
  have haB : a ∉ B := by
    intro haB
    have hh : a ∈ A ∩ B := Finset.mem_inter.mpr ⟨hA.2.1,haB⟩
    rw [hi] at hh
    exact hA.2.2.2.1 (Finset.mem_singleton.mp hh)
  have hbA : b ∉ A := by
    intro hbA
    have hh : b ∈ A ∩ B := Finset.mem_inter.mpr ⟨hbA,hB.2.1⟩
    rw [hi] at hh
    exact hB.2.2.2.1 (Finset.mem_singleton.mp hh)
  have hab : a ≠ b := by intro he; exact haB (he.symm ▸ hB.2.1)
  have hU : A ∪ B ⊆ M.atoms := by
    intro z hz
    exact (Finset.mem_union.mp hz).elim (fun hh => hA.1 hh) (fun hh => hB.1 hh)
  have haU := Finset.mem_union_left B hA.2.1
  have hbU := Finset.mem_union_right A hB.2.1
  have hinterior := concatenation_interior_degree M hM hA hB hcA hi
  have hdega := concatenation_endpoint_degree M hM hA hB hi
  have hdegb := concatenation_endpoint_degree M hM hB hA (by rw [Finset.inter_comm,hi])
  rw [Finset.union_comm,bondsBetween_symm M b a] at hdegb
  have hsig := concatenation_cross_bonds_le_one M hM hA hB hcA hi
  have hoa := hA.2.2.2.2.1
  have hia := hA.2.2.2.2.2.1
  have hob := hB.2.2.2.2.1
  have hib := hB.2.2.2.2.2.1
  have hconn := LGSpine.source_groupConnected_union M
    hA.2.2.2.2.2.2.2.2.2 hB.2.2.2.2.2.2.2.2.2 hA.2.2.1 hB.2.2.1
  by_cases hs : M.bondsBetween a b = 0
  · left
    have ho1 := outIn_mono M (Finset.subset_union_left : A ⊆ A ∪ B) a
    have hi1 := inIn_mono M (Finset.subset_union_left : A ⊆ A ∪ B) a
    have ho2 := outIn_mono M (Finset.subset_union_right : B ⊆ A ∪ B) b
    have hi2 := inIn_mono M (Finset.subset_union_right : B ⊆ A ∪ B) b
    have hsum1 := outIn_add_inIn M (A ∪ B) a
    have hsum2 := outIn_add_inIn M (A ∪ B) b
    refine ⟨hU,haU,hbU,hab,?_,?_,?_,?_,hinterior,hconn⟩ <;> omega
  · right
    have hs1 : M.bondsBetween a b = 1 := by omega
    have hne : (M.bonds.filter (fun e => M.ends e = s(a,b))).Nonempty := by
      apply Finset.card_pos.mp
      change 0 < M.bondsBetween a b
      omega
    obtain ⟨e,hemem⟩ := hne
    have he := (Finset.mem_filter.mp hemem).2
    have hend : (M.atom e = a ∧ M.atom (M.mate e) = b) ∨
        (M.atom e = b ∧ M.atom (M.mate e) = a) := Sym2.eq_iff.mp he
    have hnotA : ¬ M.InGroup A e := by
      intro hg
      rcases hend with hh | hh
      · exact hbA (hh.2 ▸ hg.2)
      · exact hbA (hh.1 ▸ hg.1)
    have hnotB : ¬ M.InGroup B e := by
      intro hg
      rcases hend with hh | hh
      · exact haB (hh.1 ▸ hg.1)
      · exact haB (hh.2 ▸ hg.2)
    have hAE := ((Vine.eraseBond_local_embedding M e A hnotA).isBlock_iff A
      (Finset.Subset.refl A) a c).mpr hA
    have hBE := ((Vine.eraseBond_local_embedding M e B hnotB).isBlock_iff B
      (Finset.Subset.refl B) b c).mpr hB
    have hconnE := LGSpine.source_groupConnected_union (eraseBond M e)
      hAE.2.2.2.2.2.2.2.2.2 hBE.2.2.2.2.2.2.2.2.2 hA.2.2.1 hB.2.2.1
    have hoAE : (eraseBond M e).outIn A a = M.outIn A a := eraseBond_orientedIn M e A a true hnotA
    have hiAE : (eraseBond M e).inIn A a = M.inIn A a := eraseBond_orientedIn M e A a false hnotA
    have hoBE : (eraseBond M e).outIn B b = M.outIn B b := eraseBond_orientedIn M e B b true hnotB
    have hiBE : (eraseBond M e).inIn B b = M.inIn B b := eraseBond_orientedIn M e B b false hnotB
    have ho1 := outIn_mono (eraseBond M e) (Finset.subset_union_left : A ⊆ A ∪ B) a
    have hi1 := inIn_mono (eraseBond M e) (Finset.subset_union_left : A ⊆ A ∪ B) a
    have ho2 := outIn_mono (eraseBond M e) (Finset.subset_union_right : B ⊆ A ∪ B) b
    have hi2 := inIn_mono (eraseBond M e) (Finset.subset_union_right : B ⊆ A ∪ B) b
    rw [hoAE] at ho1
    rw [hiAE] at hi1
    rw [hoBE] at ho2
    rw [hiBE] at hi2
    have hsum1 := outIn_add_inIn (eraseBond M e) (A ∪ B) a
    have hsum2 := outIn_add_inIn (eraseBond M e) (A ∪ B) b
    obtain ⟨hd1,hd2⟩ := eraseBond_joint_degrees M e he hab haU hbU
    refine ⟨e,he,hU,haU,hbU,hab,?_,?_,?_,?_,?_,hconnE⟩
    · omega
    · omega
    · omega
    · omega
    · intro z hz hza hzb
      have hn1 : M.atom e ≠ z := by
        rcases hend with ⟨ha,hb⟩ | ⟨ha,hb⟩
        · exact fun hh => hza (hh.symm.trans ha)
        · exact fun hh => hzb (hh.symm.trans ha)
      have hn2 : M.atom (M.mate e) ≠ z := by
        rcases hend with ⟨ha,hb⟩ | ⟨ha,hb⟩
        · exact fun hh => hzb (hh.symm.trans hb)
        · exact fun hh => hza (hh.symm.trans hb)
      rw [eraseBond_degIn_other M e hn1 hn2]
      exact hinterior z hz hza hzb

end WaveTurbulence.Mole
