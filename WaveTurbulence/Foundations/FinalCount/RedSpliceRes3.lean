/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceDarts
public import WaveTurbulence.Foundations.Spine.SourceJointPairDichotomy
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a): the residual of the skipped vine of a group (H1-H3)

Abstract form (any molecule `N` and merge labelling `cls`): the group `S = L0 ∪ A ∪ R0` is a block, `A` a
block with joints `x, y`, the runs `L0` (joints `a, x`) and `R0` (joints `y, b`) are blocks meeting `A` only
in `x`, `y` and are collapsed to single classes.  Then the hypotheses H1-H3 of `SpMol.inducedIso` hold for
`B = A`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A block `S` cut around the sub-block `A` into two runs (no merge labelling yet). -/
structure SkelDecomp (N : Molecule V D) (S A L0 R0 : Finset V) (a b x y : V) : Prop where
  mol : N.IsMolecule
  hS : S = L0 ∪ A ∪ R0
  hSB : N.IsBlock S a b
  hA : N.IsBlock A x y
  hL : L0 = ∅ ∧ x = a ∨ (x ≠ a ∧ N.IsBlock L0 a x ∧ L0 ∩ A = {x})
  hR : R0 = ∅ ∧ y = b ∨ (y ≠ b ∧ N.IsBlock R0 y b ∧ R0 ∩ A = {y})
  hd : Disjoint L0 R0

/-- A block `S` cut around the sub-block `A` into two collapsed runs. -/
structure SDecomp (N : Molecule V D) (cls : V → Option V) (S A L0 R0 : Finset V) (a b x y : V) : Prop
    extends SkelDecomp N S A L0 R0 a b x y where
  hcls : ∀ v r, cls v = some r → cls r = some r
  hLcl : ∀ p v, v ∈ L0 → (cls p).getD p = (cls v).getD v → p ∈ L0
  hRcl : ∀ p v, v ∈ R0 → (cls p).getD p = (cls v).getD v → p ∈ R0
  hLc : ∀ p ∈ L0, ∀ q ∈ L0, ∃ r, cls p = some r ∧ cls q = some r
  hRc : ∀ p ∈ R0, ∀ q ∈ R0, ∃ r, cls p = some r ∧ cls q = some r
  hNone : ∀ v ∈ S, v ∉ L0 → v ∉ R0 → cls v = none

namespace SDecomp
variable {N : Molecule V D} {cls : V → Option V} {S A L0 R0 : Finset V} {a b x y : V}
  (H : SDecomp N cls S A L0 R0 a b x y)
include H

theorem hAsub : A ⊆ S := by rw [H.hS]; exact fun v hv => mem_union_left _ (mem_union_right _ hv)
theorem hLsub : L0 ⊆ S := by rw [H.hS]; exact fun v hv => mem_union_left _ (mem_union_left _ hv)
theorem hRsub : R0 ⊆ S := by rw [H.hS]; exact fun v hv => mem_union_right _ hv

theorem hxA : x ∈ A := H.hA.2.1
theorem hyA : y ∈ A := H.hA.2.2.1
theorem hxy : x ≠ y := H.hA.2.2.2.1

theorem xL (hL : L0 ≠ ∅) : x ∈ L0 := by
  rcases H.hL with ⟨h, _⟩ | ⟨_, _, hi⟩
  · exact absurd h hL
  · have : x ∈ L0 ∩ A := by rw [hi]; exact mem_singleton_self _
    exact (mem_inter.mp this).1

theorem yR (hR : R0 ≠ ∅) : y ∈ R0 := by
  rcases H.hR with ⟨h, _⟩ | ⟨_, _, hi⟩
  · exact absurd h hR
  · have : y ∈ R0 ∩ A := by rw [hi]; exact mem_singleton_self _
    exact (mem_inter.mp this).1

/-- The classes of atoms of the vine. -/
theorem class_of (p v : V) (hv : v ∈ A) (h : (cls p).getD p = (cls v).getD v) :
    p ∈ L0 ∨ p ∈ R0 ∨ p = v := by
  by_cases hvL : v ∈ L0
  · exact Or.inl (H.hLcl p v hvL h)
  · by_cases hvR : v ∈ R0
    · exact Or.inr (Or.inl (H.hRcl p v hvR h))
    · have hnone : cls v = none := H.hNone v (H.hAsub hv) hvL hvR
      rw [hnone] at h
      simp only [Option.getD_none] at h
      right; right
      cases hp : cls p with
      | none => rw [hp] at h; simpa using h
      | some r =>
        rw [hp] at h
        simp only [Option.getD_some] at h
        subst h
        have := H.hcls p r hp
        rw [hnone] at this
        cases this

theorem H1 : ∀ u ∈ A, ∀ v ∈ A, (cls u).getD u = (cls v).getD v → u = v := by
  intro u hu v hv h
  by_cases huL : u ∈ L0
  · have hvL : v ∈ L0 := H.hLcl v u huL h.symm
    rcases H.hL with ⟨h0, _⟩ | ⟨_, _, hi⟩
    · rw [h0] at huL; simp at huL
    · have h1 : u ∈ L0 ∩ A := mem_inter.mpr ⟨huL, hu⟩
      have h2 : v ∈ L0 ∩ A := mem_inter.mpr ⟨hvL, hv⟩
      rw [hi, mem_singleton] at h1 h2
      exact h1.trans h2.symm
  · by_cases huR : u ∈ R0
    · have hvR : v ∈ R0 := H.hRcl v u huR h.symm
      rcases H.hR with ⟨h0, _⟩ | ⟨_, _, hi⟩
      · rw [h0] at huR; simp at huR
      · have h1 : u ∈ R0 ∩ A := mem_inter.mpr ⟨huR, hu⟩
        have h2 : v ∈ R0 ∩ A := mem_inter.mpr ⟨hvR, hv⟩
        rw [hi, mem_singleton] at h1 h2
        exact h1.trans h2.symm
    · have hnone := H.hNone u (H.hAsub hu) huL huR
      rcases H.class_of v u hu h.symm with hvL | hvR | hvu
      · exfalso
        exact huL (by
          rcases H.hL with ⟨h0, _⟩ | ⟨_, _, hi⟩
          · rw [h0] at hvL; simp at hvL
          · have h2 : v ∈ L0 ∩ A := mem_inter.mpr ⟨hvL, hv⟩
            rw [hi, mem_singleton] at h2
            -- then u's class equals that of the crown: contradiction with `hnone`
            subst h2
            exfalso
            exact absurd (H.hLcl u v hvL h) huL)
      · exfalso
        rcases H.hR with ⟨h0, _⟩ | ⟨_, _, hi⟩
        · rw [h0] at hvR; simp at hvR
        · have h2 : v ∈ R0 ∩ A := mem_inter.mpr ⟨hvR, hv⟩
          rw [hi, mem_singleton] at h2
          subst h2
          exact huR (H.hRcl u v hvR h)
      · exact hvu.symm

theorem noLoopX {d : D} (hd : N.InGroup A d) (hp : N.atom d = x) : N.atom (N.mate d) ≠ x := by
  have hc : Mole.GroupConnected N A := LGSpine.groupConnected_of_block H.hA
  exact connected_degree_two_no_loop N hc H.hxA H.hyA (Ne.symm H.hxy) (block_joint_degrees N H.hA).1 hp

theorem noLoopY {d : D} (hd : N.InGroup A d) (hp : N.atom d = y) : N.atom (N.mate d) ≠ y := by
  have hc : Mole.GroupConnected N A := LGSpine.groupConnected_of_block H.hA
  exact connected_degree_two_no_loop N hc H.hyA H.hxA H.hxy (block_joint_degrees N H.hA).2 hp

theorem H2 : ∀ d, N.InGroup A d →
    ¬ ∃ r, cls (N.atom d) = some r ∧ cls (N.atom (N.mate d)) = some r := by
  rintro d hd ⟨r, h1, h2⟩
  have hpq : N.atom d = N.atom (N.mate d) := by
    apply H.H1 _ hd.1 _ hd.2
    rw [h1, h2]; rfl
  have hp := hd.1
  have hS := H.hAsub hp
  by_cases hL : N.atom d ∈ L0
  · have hx : N.atom d = x := by
      rcases H.hL with ⟨h0, _⟩ | ⟨_, _, hi⟩
      · rw [h0] at hL; simp at hL
      · have : N.atom d ∈ L0 ∩ A := mem_inter.mpr ⟨hL, hp⟩
        rw [hi, mem_singleton] at this
        exact this
    exact H.noLoopX hd hx (hpq ▸ hx)
  · by_cases hR : N.atom d ∈ R0
    · have hy : N.atom d = y := by
        rcases H.hR with ⟨h0, _⟩ | ⟨_, _, hi⟩
        · rw [h0] at hR; simp at hR
        · have : N.atom d ∈ R0 ∩ A := mem_inter.mpr ⟨hR, hp⟩
          rw [hi, mem_singleton] at this
          exact this
      exact H.noLoopY hd hy (hpq ▸ hy)
    · have := H.hNone _ hS hL hR
      rw [this] at h1
      cases h1

theorem classInt_L {d : D} (hp : N.InGroup L0 d) :
    ∃ r, cls (N.atom d) = some r ∧ cls (N.atom (N.mate d)) = some r := H.hLc _ hp.1 _ hp.2

theorem classInt_R {d : D} (hp : N.InGroup R0 d) :
    ∃ r, cls (N.atom d) = some r ∧ cls (N.atom (N.mate d)) = some r := H.hRc _ hp.1 _ hp.2

theorem xb (hL : L0 ≠ ∅) : x ≠ b := by
  intro hxb
  rcases H.hR with ⟨_, hyb⟩ | ⟨_, hRB, _⟩
  · exact H.hxy (hxb.trans hyb.symm)
  · have hbR : b ∈ R0 := hRB.2.2.1
    have hxL := H.xL hL
    exact Finset.disjoint_left.mp H.hd hxL (hxb ▸ hbR)

theorem ya (hR : R0 ≠ ∅) : y ≠ a := by
  intro hya
  rcases H.hL with ⟨_, hxa⟩ | ⟨_, hLB, _⟩
  · exact H.hxy (hxa.trans hya.symm)
  · have haL : a ∈ L0 := hLB.2.1
    have hyR := H.yR hR
    exact Finset.disjoint_left.mp H.hd (hya ▸ haL) hyR

/-- A non-class-internal `S`-internal dart at an atom of the vine is internal to the vine. -/
theorem Aint {d : D} (hS : N.InGroup S d) (hnc : ¬ ∃ r, cls (N.atom d) = some r ∧ cls (N.atom (N.mate d)) = some r)
    (hp : N.atom d ∈ A) : N.InGroup A d := by
  by_cases hpx : N.atom d = x
  · by_cases hL : L0 = ∅
    · have hxa : x = a := by
        rcases H.hL with ⟨_, h⟩ | ⟨_, _, hi⟩
        · exact h
        · exfalso
          have : x ∈ L0 ∩ A := by rw [hi]; exact mem_singleton_self _
          rw [hL] at this
          simp at this
      have hdeg : N.degIn A x = N.degIn S x := by
        rw [(block_joint_degrees N H.hA).1, hxa, (block_joint_degrees N H.hSB).1]
      exact subEq H.hAsub hdeg hpx hS
    · obtain ⟨hxa, hLB, hi⟩ : x ≠ a ∧ N.IsBlock L0 a x ∧ L0 ∩ A = {x} := by
        rcases H.hL with ⟨h, _⟩ | h
        · exact absurd h hL
        · exact h
      have hxL := H.xL hL
      have hdis : ∀ d', N.InGroup A d' → N.InGroup L0 d' → False := by
        intro d' h1 h2
        have e1 : N.atom d' ∈ L0 ∩ A := mem_inter.mpr ⟨h2.1, h1.1⟩
        have e2 : N.atom (N.mate d') ∈ L0 ∩ A := mem_inter.mpr ⟨h2.2, h1.2⟩
        rw [hi, mem_singleton] at e1 e2
        exact H.noLoopX h1 e1 e2
      rcases splitTwo H.mol H.hxA hxL hdis (block_joint_degrees N H.hA).1 (block_joint_degrees N hLB).2
          (H.hA.1 H.hxA) hpx with h | h
      · exact h
      · exact absurd (H.classInt_L h) hnc
  · by_cases hpy : N.atom d = y
    · by_cases hR : R0 = ∅
      · have hyb : y = b := by
          rcases H.hR with ⟨_, h⟩ | ⟨_, _, hi⟩
          · exact h
          · exfalso
            have : y ∈ R0 ∩ A := by rw [hi]; exact mem_singleton_self _
            rw [hR] at this
            simp at this
        have hdeg : N.degIn A y = N.degIn S y := by
          rw [(block_joint_degrees N H.hA).2, hyb, (block_joint_degrees N H.hSB).2]
        exact subEq H.hAsub hdeg hpy hS
      · obtain ⟨hyb, hRB, hi⟩ : y ≠ b ∧ N.IsBlock R0 y b ∧ R0 ∩ A = {y} := by
          rcases H.hR with ⟨h, _⟩ | h
          · exact absurd h hR
          · exact h
        have hyR := H.yR hR
        have hdis : ∀ d', N.InGroup A d' → N.InGroup R0 d' → False := by
          intro d' h1 h2
          have e1 : N.atom d' ∈ R0 ∩ A := mem_inter.mpr ⟨h2.1, h1.1⟩
          have e2 : N.atom (N.mate d') ∈ R0 ∩ A := mem_inter.mpr ⟨h2.2, h1.2⟩
          rw [hi, mem_singleton] at e1 e2
          exact H.noLoopY h1 e1 e2
        rcases splitTwo H.mol H.hyA hyR hdis (block_joint_degrees N H.hA).2 (block_joint_degrees N hRB).1
            (H.hA.1 H.hyA) hpy with h | h
        · exact h
        · exact absurd (H.classInt_R h) hnc
    · exact allInt H.mol H.hA hp hpx hpy rfl

theorem notL {d : D} (hS : N.InGroup S d)
    (hnc : ¬ ∃ r, cls (N.atom d) = some r ∧ cls (N.atom (N.mate d)) = some r)
    (hL : N.atom d ∈ L0) : N.atom d ∈ A := by
  by_contra hpA
  have hL0 : L0 ≠ ∅ := fun h => by rw [h] at hL; simp at hL
  obtain ⟨hxa, hLB, hi⟩ : x ≠ a ∧ N.IsBlock L0 a x ∧ L0 ∩ A = {x} := by
    rcases H.hL with ⟨h, _⟩ | h
    · exact absurd h hL0
    · exact h
  have hpx : N.atom d ≠ x := fun h => hpA (h ▸ H.hxA)
  by_cases hpa : N.atom d = a
  · have hdeg : N.degIn L0 a = N.degIn S a := by
      rw [(block_joint_degrees N hLB).1, (block_joint_degrees N H.hSB).1]
    exact hnc (H.classInt_L (subEq H.hLsub hdeg hpa hS))
  · exact hnc (H.classInt_L (allInt H.mol hLB hL hpa hpx rfl))

theorem notR {d : D} (hS : N.InGroup S d)
    (hnc : ¬ ∃ r, cls (N.atom d) = some r ∧ cls (N.atom (N.mate d)) = some r)
    (hR : N.atom d ∈ R0) : N.atom d ∈ A := by
  by_contra hpA
  have hR0 : R0 ≠ ∅ := fun h => by rw [h] at hR; simp at hR
  obtain ⟨hyb, hRB, hi⟩ : y ≠ b ∧ N.IsBlock R0 y b ∧ R0 ∩ A = {y} := by
    rcases H.hR with ⟨h, _⟩ | h
    · exact absurd h hR0
    · exact h
  have hpy : N.atom d ≠ y := fun h => hpA (h ▸ H.hyA)
  by_cases hpb : N.atom d = b
  · have hdeg : N.degIn R0 b = N.degIn S b := by
      rw [(block_joint_degrees N hRB).2, (block_joint_degrees N H.hSB).2]
    exact hnc (H.classInt_R (subEq H.hRsub hdeg hpb hS))
  · exact hnc (H.classInt_R (allInt H.mol hRB hR hpy hpb rfl))

theorem H3 : ∀ d, (∃ v ∈ A, (cls (N.atom d)).getD (N.atom d) = (cls v).getD v) →
    (∃ v ∈ A, (cls (N.atom (N.mate d))).getD (N.atom (N.mate d)) = (cls v).getD v) →
    (¬ ∃ r, cls (N.atom d) = some r ∧ cls (N.atom (N.mate d)) = some r) → N.InGroup A d := by
  intro d ⟨v, hv, h1⟩ ⟨v', hv', h2⟩ hnc
  have hsub : ∀ p v, v ∈ A → (cls p).getD p = (cls v).getD v → p ∈ S := by
    intro p v hv h
    rcases H.class_of p v hv h with h | h | h
    · exact H.hLsub h
    · exact H.hRsub h
    · exact h ▸ H.hAsub hv
  have hS : N.InGroup S d := ⟨hsub _ v hv h1, hsub _ v' hv' h2⟩
  have hA : ∀ d', N.InGroup S d' → (¬ ∃ r, cls (N.atom d') = some r ∧ cls (N.atom (N.mate d')) = some r) →
      (∃ v ∈ A, (cls (N.atom d')).getD (N.atom d') = (cls v).getD v) → N.atom d' ∈ A := by
    intro d' hS' hnc' ⟨v, hv, h⟩
    rcases H.class_of _ v hv h with h | h | h
    · exact H.notL hS' hnc' h
    · exact H.notR hS' hnc' h
    · exact h ▸ hv
  have hp : N.atom d ∈ A := hA d hS hnc ⟨v, hv, h1⟩
  exact H.Aint hS hnc hp

theorem bL : b ∉ L0 := by
  intro hb
  rcases H.hR with ⟨_, hyb⟩ | ⟨_, hRB, _⟩
  · rcases H.hL with ⟨h0, _⟩ | ⟨_, _, hi⟩
    · rw [h0] at hb; simp at hb
    · have : b ∈ L0 ∩ A := mem_inter.mpr ⟨hb, hyb ▸ H.hyA⟩
      rw [hi, mem_singleton] at this
      exact H.hxy (this.symm.trans hyb.symm)
  · exact Finset.disjoint_left.mp H.hd hb hRB.2.2.1

theorem aR : a ∉ R0 := by
  intro ha
  rcases H.hL with ⟨_, hxa⟩ | ⟨_, hLB, _⟩
  · rcases H.hR with ⟨h0, _⟩ | ⟨_, _, hi⟩
    · rw [h0] at ha; simp at ha
    · have : a ∈ R0 ∩ A := mem_inter.mpr ⟨ha, hxa ▸ H.hxA⟩
      rw [hi, mem_singleton] at this
      exact H.hxy (hxa.trans this)
  · exact Finset.disjoint_right.mp H.hd ha hLB.2.1

theorem x_notR : x ∉ R0 := by
  intro hxR
  rcases H.hR with ⟨h0, _⟩ | ⟨_, _, hi⟩
  · rw [h0] at hxR; simp at hxR
  · have : x ∈ R0 ∩ A := mem_inter.mpr ⟨hxR, H.hxA⟩
    rw [hi, mem_singleton] at this
    exact H.hxy this

theorem y_notL : y ∉ L0 := by
  intro hyL
  rcases H.hL with ⟨h0, _⟩ | ⟨_, _, hi⟩
  · rw [h0] at hyL; simp at hyL
  · have : y ∈ L0 ∩ A := mem_inter.mpr ⟨hyL, H.hyA⟩
    rw [hi, mem_singleton] at this
    exact H.hxy this.symm

/-- The class of the joint `x`. -/
theorem classx {p : V} (hp : (cls p).getD p = (cls x).getD x) :
    (x ∈ L0 ∧ p ∈ L0) ∨ (x ∉ L0 ∧ p = x) := by
  by_cases hxL : x ∈ L0
  · exact Or.inl ⟨hxL, H.hLcl p x hxL hp⟩
  · right
    refine ⟨hxL, ?_⟩
    rcases H.class_of p x H.hxA hp with h | h | h
    · exact absurd (H.hLcl x p h hp.symm) hxL
    · exact absurd (H.hRcl x p h hp.symm) H.x_notR
    · exact h

/-- Only the joints of the vine are merged. -/
theorem hinge_cases {z : V} (hz : z ∈ A) (h : cls ((cls z).getD z) ≠ none) : z = x ∨ z = y := by
  by_cases hzL : z ∈ L0
  · left
    rcases H.hL with ⟨h0, _⟩ | ⟨_, _, hi⟩
    · rw [h0] at hzL; simp at hzL
    · have : z ∈ L0 ∩ A := mem_inter.mpr ⟨hzL, hz⟩
      rw [hi, mem_singleton] at this
      exact this
  · by_cases hzR : z ∈ R0
    · right
      rcases H.hR with ⟨h0, _⟩ | ⟨_, _, hi⟩
      · rw [h0] at hzR; simp at hzR
      · have : z ∈ R0 ∩ A := mem_inter.mpr ⟨hzR, hz⟩
        rw [hi, mem_singleton] at this
        exact this
    · exfalso
      have hn := H.hNone z (H.hAsub hz) hzL hzR
      apply h
      rw [hn]
      simp [hn]

theorem rc_a : (cls a).getD a = (cls x).getD x := by
  rcases H.hL with ⟨_, h⟩ | ⟨hxa, hLB, hi⟩
  · rw [h]
  · have haL : a ∈ L0 := hLB.2.1
    have hxL : x ∈ L0 := hLB.2.2.1
    obtain ⟨r, h1, h2⟩ := H.hLc a haL x hxL
    rw [h1, h2]; rfl

theorem rc_b : (cls b).getD b = (cls y).getD y := by
  rcases H.hR with ⟨_, h⟩ | ⟨hyb, hRB, hi⟩
  · rw [h]
  · have hbR : b ∈ R0 := hRB.2.2.1
    have hyR : y ∈ R0 := hRB.2.1
    obtain ⟨r, h1, h2⟩ := H.hRc b hbR y hyR
    rw [h1, h2]; rfl

/-- The two end joints of the group are not in a common class. -/
theorem ends_not_class : ¬ ∃ r, cls a = some r ∧ cls b = some r := by
  rintro ⟨r, h1, h2⟩
  have haS : a ∈ S := H.hSB.2.1
  have hbS : b ∈ S := H.hSB.2.2.1
  have haL : a ∈ L0 := by
    by_contra haL
    have := H.hNone a haS haL H.aR
    rw [this] at h1; cases h1
  have hbR : b ∈ R0 := by
    by_contra hbR
    have := H.hNone b hbS H.bL hbR
    rw [this] at h2; cases h2
  have : (cls b).getD b = (cls a).getD a := by rw [h1, h2]; rfl
  exact H.bL (H.hLcl b a haL this)

end SDecomp

/-- The mirror image of a decomposition (exchange the two runs). -/
theorem SDecomp.symm {N : Molecule V D} {cls : V → Option V} {S A L0 R0 : Finset V}
    {a b x y : V} (H : SDecomp N cls S A L0 R0 a b x y) :
    SDecomp N cls S A R0 L0 b a y x where
  mol := H.mol
  hS := by
    rw [H.hS]
    ext v
    simp only [mem_union]
    tauto
  hSB := Mole.block_swap_joints N H.hSB
  hA := Mole.block_swap_joints N H.hA
  hL := by
    rcases H.hR with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, Mole.block_swap_joints N h2, h3⟩
  hR := by
    rcases H.hL with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, Mole.block_swap_joints N h2, h3⟩
  hd := H.hd.symm
  hcls := H.hcls
  hLcl := H.hRcl
  hRcl := H.hLcl
  hLc := H.hRc
  hRc := H.hLc
  hNone := fun v hv h1 h2 => H.hNone v hv h2 h1


end WaveTurbulence.RedSplice
