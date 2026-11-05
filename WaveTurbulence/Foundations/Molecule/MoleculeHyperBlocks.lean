/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeBondEdits
import Mathlib.Tactic

/-!
# Actual half-edge realizations of hyper-blocks

TARGET `defblock`, DH23 Definition 4.10: deleting the designated added
joint-to-joint bond gives the adjoint block. All counts retain multiplicity.
-/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

/-- The internal incidences of a bond deletion are exactly the original
internal incidences minus the two deleted mates. -/
theorem eraseBond_degIn (e : D) (S : Finset V) (v : V) :
    (eraseBond M e).degIn S v =
      (((M.dartsAt v).filter (M.InGroup S)) \ {e,M.mate e}).card := by
  unfold Molecule.degIn
  apply Finset.card_bij (fun x _hx => x.1)
  · intro x hx
    obtain ⟨hxv,hxg⟩ := Finset.mem_filter.mp hx
    have hv := (mem_dartsAt (eraseBond M e) v x).mp hxv
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_filter.mpr ⟨(mem_dartsAt M v x.1).mpr hv,hxg⟩,?_⟩
    simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using x.2
  · intro x hx y hy he
    exact Subtype.ext he
  · intro x hx
    obtain ⟨hxv,hxne⟩ := Finset.mem_sdiff.mp hx
    have hn : x ≠ e ∧ x ≠ M.mate e := by
      simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hxne
    refine ⟨⟨x,hn⟩,Finset.mem_filter.mpr ⟨?_,(Finset.mem_filter.mp hxv).2⟩,rfl⟩
    exact (mem_dartsAt (eraseBond M e) v ⟨x,hn⟩).mpr ((mem_dartsAt M v x).mp (Finset.mem_filter.mp hxv).1)

/-- Deleting a bond removes one incidence at each distinct endpoint. -/
theorem eraseBond_degIn_endpoint (e : D) {a b : V} (ha : M.atom e = a)
    (hb : M.atom (M.mate e) = b) (hne : a ≠ b) {S : Finset V} (haS : a ∈ S) (hbS : b ∈ S) :
    (eraseBond M e).degIn S a+1 = M.degIn S a := by
  rw [eraseBond_degIn]
  let T := (M.dartsAt a).filter (M.InGroup S)
  have he : e ∈ T := Finset.mem_filter.mpr ⟨(mem_dartsAt _ _ _).mpr ha,ha.symm ▸ haS,hb.symm ▸ hbS⟩
  have hm : M.mate e ∉ T := by
    intro hm
    have hm' := (mem_dartsAt _ _ _).mp (Finset.mem_filter.mp hm).1
    exact hne (hm'.symm.trans hb)
  have hs : T \ {e,M.mate e} = T.erase e := by
    ext x
    simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton,not_or,Finset.mem_erase]
    constructor
    · rintro ⟨hx,h1,h2⟩
      exact ⟨h1,hx⟩
    · rintro ⟨h1,hx⟩
      exact ⟨hx,h1,fun he => hm (he ▸ hx)⟩
  change (T \ {e,M.mate e}).card+1 = T.card
  rw [hs]
  exact Finset.card_erase_add_one he

/-- Removing a bond leaves every other internal degree unchanged. -/
theorem eraseBond_degIn_other (e : D) {v : V} (h1 : M.atom e ≠ v)
    (h2 : M.atom (M.mate e) ≠ v) (S : Finset V) :
    (eraseBond M e).degIn S v = M.degIn S v := by
  rw [eraseBond_degIn]
  congr 1
  apply Finset.sdiff_eq_self_iff_disjoint.mpr
  apply Finset.disjoint_right.mpr
  intro x hx hxv
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  have hv := (mem_dartsAt _ _ _).mp (Finset.mem_filter.mp hxv).1
  rcases hx with rfl | rfl
  · exact h1 hv
  · exact h2 hv

/-- Deleting a bond is independent of which mate represents it. -/
theorem eraseBond_mate_degIn (e : D) (S : Finset V) (v : V) :
    (eraseBond M (M.mate e)).degIn S v = (eraseBond M e).degIn S v := by
  rw [eraseBond_degIn,eraseBond_degIn,M.mate_mate,Finset.pair_comm]

/-- Every actual hyper-block realization has degree-three joints and
degree-four interior atoms, as asserted by the source adjoint construction. -/
theorem hyperBlock_degrees {S : Finset V} {j1 j2 : V} (hH : IsHyperBlock M S j1 j2) :
    M.degIn S j1 = 3 ∧ M.degIn S j2 = 3 ∧
      ∀ v ∈ S, v ≠ j1 → v ≠ j2 → M.degIn S v = 4 := by
  obtain ⟨e,he,hB⟩ := hH
  have hne := hB.2.2.2.1
  obtain ⟨hd1,hd2⟩ := block_joint_degrees (eraseBond M e) hB
  have hend := Sym2.eq_iff.mp he
  change (M.atom e = j1 ∧ M.atom (M.mate e) = j2) ∨
    (M.atom e = j2 ∧ M.atom (M.mate e) = j1) at hend
  have hdeg : M.degIn S j1 = 3 ∧ M.degIn S j2 = 3 := by
    rcases hend with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · have h1 := eraseBond_degIn_endpoint M e ha hb hne hB.2.1 hB.2.2.1
      have h2 := eraseBond_degIn_endpoint M (M.mate e) hb (by rw [M.mate_mate]; exact ha)
        (Ne.symm hne) hB.2.2.1 hB.2.1
      rw [eraseBond_mate_degIn] at h2
      omega
    · have h1 := eraseBond_degIn_endpoint M e ha hb (Ne.symm hne) hB.2.2.1 hB.2.1
      have h2 := eraseBond_degIn_endpoint M (M.mate e) hb (by rw [M.mate_mate]; exact ha)
        hne hB.2.1 hB.2.2.1
      rw [eraseBond_mate_degIn] at h2
      omega
  refine ⟨hdeg.1,hdeg.2,?_⟩
  intro v hv h1 h2
  have hinner := hB.2.2.2.2.2.2.2.2.1 v hv h1 h2
  have hnot1 : M.atom e ≠ v := by rcases hend with h|h <;> rcases h with ⟨ha,hb⟩ <;> rw [ha] <;> exact Ne.symm (by assumption)
  have hnot2 : M.atom (M.mate e) ≠ v := by rcases hend with h|h <;> rcases h with ⟨ha,hb⟩ <;> rw [hb] <;> exact Ne.symm (by assumption)
  rw [eraseBond_degIn_other M e hnot1 hnot2 S] at hinner
  exact hinner

end WaveTurbulence.Mole
