/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceExt
import Mathlib.Tactic

/-!
# SUBPRO (S4): geometry of block joints

* interior atoms of a block have no external dart (degrees are at most four);
* a joint has at most two external darts;
* a joint carries no self-loop of the block.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

theorem degIn_eq (S : Finset V) (v : V) : M.degIn S v = M.outIn S v + M.inIn S v := by
  classical
  unfold Molecule.degIn Molecule.outIn Molecule.inIn
  have := Finset.card_filter_add_card_filter_not (s := (M.dartsAt v).filter fun x => M.InGroup S x)
    (fun x => M.out x = true)
  rw [Finset.filter_filter, Finset.filter_filter] at this
  have h2 : ((M.dartsAt v).filter fun x => M.InGroup S x ∧ ¬ M.out x = true) =
      ((M.dartsAt v).filter fun x => M.InGroup S x ∧ M.out x = false) := by
    apply Finset.filter_congr
    intro x _
    simp
  rw [h2] at this
  omega

theorem block_interior_ext (hM : M.IsMolecule) {S : Finset V} {a b : V} (hB : M.IsBlock S a b) {v : V} (hv : v ∈ S)
    (ha : v ≠ a) (hb : v ≠ b) {d : D} (hd : M.atom d = v) : M.InGroup S d := by
  classical
  have h4 : M.degIn S v = 4 := hB.2.2.2.2.2.2.2.2.1 v hv ha hb
  have hle : M.deg v ≤ 4 := deg_le_four M hM (hB.1 hv)
  have hsub : (M.dartsAt v).filter (fun x => M.InGroup S x) ⊆ M.dartsAt v := Finset.filter_subset _ _
  have heq : (M.dartsAt v).filter (fun x => M.InGroup S x) = M.dartsAt v :=
    Finset.eq_of_subset_of_card_le hsub (by
      have : ((M.dartsAt v).filter (fun x => M.InGroup S x)).card = 4 := h4
      unfold Molecule.deg at hle
      omega)
  have : d ∈ M.dartsAt v := by simp [Molecule.dartsAt, hd]
  rw [← heq] at this
  exact (Finset.mem_filter.mp this).2

/-- A joint of a block has at most two external darts. -/
theorem joint_ext_card (hM : M.IsMolecule) {S : Finset V} {a b : V} (hB : M.IsBlock S a b) :
    ((M.dartsAt a).filter (fun d => ¬ M.InGroup S d)).card ≤ 2 := by
  classical
  have h1 := Finset.card_filter_add_card_filter_not (s := M.dartsAt a) (fun x => M.InGroup S x)
  have h2 := degIn_eq (M := M) S a
  have hle : M.deg a ≤ 4 := deg_le_four M hM (hB.1 hB.2.1)
  have ho : M.outIn S a = 1 := hB.2.2.2.2.1
  have hi : M.inIn S a = 1 := hB.2.2.2.2.2.1
  unfold Molecule.degIn at h2
  unfold Molecule.deg at hle
  omega

/-- A joint of a block carries no self-loop of the block. -/
theorem block_no_loop {S : Finset V} {a b : V} (hB : M.IsBlock S a b) {d : D} (hd : M.InGroup S d)
    (h1 : M.atom d = a) : M.atom (M.mate d) ≠ a := by
  classical
  intro h2
  -- all darts of the block at `a` are `d` and `mate d`
  have ho : ((M.dartsAt a).filter fun x => M.InGroup S x ∧ M.out x = true).card = 1 := hB.2.2.2.2.1
  have hi : ((M.dartsAt a).filter fun x => M.InGroup S x ∧ M.out x = false).card = 1 := hB.2.2.2.2.2.1
  have hmd : M.InGroup S (M.mate d) := ⟨hd.2, by simpa [M.mate_mate] using hd.1⟩
  have hmem : ∀ x, M.atom x = a → M.InGroup S x → x = d ∨ x = M.mate d := by
    intro x hx hxS
    cases hxo : M.out x
    · -- in-dart
      obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hi
      have hxm : x ∈ (M.dartsAt a).filter fun x => M.InGroup S x ∧ M.out x = false := by
        simp [Molecule.dartsAt, hx, hxS, hxo]
      have hdm : ∀ z, M.atom z = a → M.InGroup S z → M.out z = false → z = y := by
        intro z hz hzS hzo
        have : z ∈ (M.dartsAt a).filter fun x => M.InGroup S x ∧ M.out x = false := by
          simp [Molecule.dartsAt, hz, hzS, hzo]
        rw [hy] at this; simpa using this
      have hxy : x = y := hdm x hx hxS hxo
      cases hdo : M.out d
      · exact Or.inl (hxy.trans (hdm d h1 hd hdo).symm)
      · have : M.out (M.mate d) = false := by rw [M.out_mate, hdo]; rfl
        exact Or.inr (hxy.trans (hdm _ h2 hmd this).symm)
    · obtain ⟨y, hy⟩ := Finset.card_eq_one.mp ho
      have hdm : ∀ z, M.atom z = a → M.InGroup S z → M.out z = true → z = y := by
        intro z hz hzS hzo
        have : z ∈ (M.dartsAt a).filter fun x => M.InGroup S x ∧ M.out x = true := by
          simp [Molecule.dartsAt, hz, hzS, hzo]
        rw [hy] at this; simpa using this
      have hxy : x = y := hdm x hx hxS hxo
      cases hdo : M.out d
      · have : M.out (M.mate d) = true := by rw [M.out_mate, hdo]; rfl
        exact Or.inr (hxy.trans (hdm _ h2 hmd this).symm)
      · exact Or.inl (hxy.trans (hdm d h1 hd hdo).symm)
  -- connectedness: the component of `a` is `{a}`
  have hconn := hB.2.2.2.2.2.2.2.2.2 a hB.2.1 b hB.2.2.1
  have key : ∀ u v, Relation.EqvGen (fun u v => ∃ x, M.InGroup S x ∧ M.atom x = u ∧ M.atom (M.mate x) = v) u v →
      (u = a ↔ v = a) := by
    intro u v huv
    induction huv with
    | rel u v hr =>
      obtain ⟨x, hxS, hxu, hxv⟩ := hr
      constructor
      · rintro rfl
        rcases hmem x hxu hxS with rfl | rfl
        · rw [← hxv]; exact h2
        · rw [← hxv, M.mate_mate]; exact h1
      · rintro rfl
        have hmx : M.InGroup S (M.mate x) := ⟨hxS.2, by simpa [M.mate_mate] using hxS.1⟩
        rcases hmem (M.mate x) hxv hmx with h | h
        · rw [← hxu, ← M.mate_mate x, h]; exact h2
        · rw [← hxu, ← M.mate_mate x, h, M.mate_mate]; exact h1
    | refl u => exact Iff.rfl
    | symm u v _ ih => exact ih.symm
    | trans u v z _ _ ih1 ih2 => exact ih1.trans ih2
  have := (key _ _ hconn).mp rfl
  exact (hB.2.2.2.1) this.symm

end WaveTurbulence.RedSplice
