/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Gardens
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Subtrees

/-! # The source predicates for embedded objects (TARGET L845–L847)

Incomparability of sub-couple roots is derived from complete pairing; it is
not an additional hypothesis. A sub-paired-tree retains the lower subtree as
its distinguished lone leaf after collapse.
-/

public section

namespace WaveTurbulence.Comb
open Finset

variable {w : ℕ} {G : Garden w}

/-- Descendant subtrees have nested leaf sets. -/
theorem leavesBelow_subset_of_isDesc {a b : GNode G.tree} (h : a.IsDesc b) :
    b.leavesBelow ⊆ a.leavesBelow := by
  intro ℓ hℓ
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    GNode.IsDesc.trans h (Finset.mem_filter.mp hℓ).2⟩

/-- A whole subtree cannot be completely paired: its signed leaf count is ±1. -/
theorem not_completelyPaired_subtree (a : GNode G.tree) :
    ¬ G.CompletelyPaired a.leavesBelow := by
  intro hc
  have hs := sum_rule G.sig (fun _ => (1 : ℤ)) (fun _ => by norm_num) a
  have hz := sum_signed_completelyPaired hc (fun _ => (1 : ℤ)) (fun _ => rfl)
  rw [hz] at hs
  have he : ((nodeSign G.sig a.1 : ℤˣ) : ℤ) = 0 := by
    simpa only [smul_eq_mul, mul_one] using hs
  exact Units.ne_zero _ he

/-- The raw source condition for a sub-couple (TARGET L846). -/
@[expose] def IsSubCouple (G : Garden w) (a b : GNode G.tree) : Prop :=
  G.CompletelyPaired (a.leavesBelow ∪ b.leavesBelow)

instance (G : Garden w) (a b : GNode G.tree) : Decidable (IsSubCouple G a b) := by
  unfold IsSubCouple
  infer_instance

/-- Complete pairing forces the two embedded roots to be incomparable. -/
theorem subCouple_incomparable {a b : GNode G.tree} (h : IsSubCouple G a b) : a.Incomparable b := by
  constructor
  · intro hab
    have hu : a.leavesBelow ∪ b.leavesBelow = a.leavesBelow :=
      Finset.union_eq_left.mpr (leavesBelow_subset_of_isDesc hab)
    exact not_completelyPaired_subtree a (hu ▸ h)
  · intro hba
    have hu : a.leavesBelow ∪ b.leavesBelow = b.leavesBelow :=
      Finset.union_eq_right.mpr (leavesBelow_subset_of_isDesc hba)
    exact not_completelyPaired_subtree b (hu ▸ h)

/-- Incomparable roots have disjoint descendant leaf sets. -/
theorem disjoint_leavesBelow_of_incomparable {a b : GNode G.tree} (h : a.Incomparable b) :
    Disjoint a.leavesBelow b.leavesBelow := by
  rw [Finset.disjoint_left]
  intro ℓ ha hb
  have ha' := (Finset.mem_filter.mp ha).2
  have hb' := (Finset.mem_filter.mp hb).2
  have hj : a.1.1 = b.1.1 := ha'.1.trans hb'.1.symm
  rcases List.prefix_or_prefix_of_prefix ha'.2 hb'.2 with hab | hba
  · exact h.1 ⟨hj, hab⟩
  · exact h.2 ⟨hj.symm, hba⟩

/-- Sub-couple root signs are opposite, as required for a genuine couple. -/
theorem subCouple_sign {a b : GNode G.tree} (h : IsSubCouple G a b) :
    G.sign b = -G.sign a := by
  have hd := disjoint_leavesBelow_of_incomparable (subCouple_incomparable h)
  have hz := sum_signed_completelyPaired h (fun _ => (1 : ℤ)) (fun _ => rfl)
  rw [Finset.sum_union hd] at hz
  have ha := sum_rule G.sig (fun _ => (1 : ℤ)) (fun _ => by norm_num) a
  have hb := sum_rule G.sig (fun _ => (1 : ℤ)) (fun _ => by norm_num) b
  rw [← ha, ← hb] at hz
  simp only [smul_eq_mul, mul_one] at hz
  apply Units.ext
  change ((nodeSign G.sig b.1 : ℤˣ) : ℤ) = -((nodeSign G.sig a.1 : ℤˣ) : ℤ)
  omega

/-- The source condition for an embedded paired tree, with lower root `b`. -/
@[expose] def IsSubPairedTree (G : Garden w) (a b : GNode G.tree) : Prop :=
  a.IsDesc b ∧ G.CompletelyPaired (a.leavesBelow \ b.leavesBelow)

instance (G : Garden w) (a b : GNode G.tree) : Decidable (IsSubPairedTree G a b) := by
  unfold IsSubPairedTree
  infer_instance

/-- The upper and lower roots of an embedded paired tree have the same sign. -/
theorem subPairedTree_sign {a b : GNode G.tree} (h : IsSubPairedTree G a b) :
    G.sign a = G.sign b := by
  have ha := sum_rule G.sig (fun _ => (1 : ℤ)) (fun _ => by norm_num) a
  have hb := sum_rule G.sig (fun _ => (1 : ℤ)) (fun _ => by norm_num) b
  have hz := sum_signed_completelyPaired h.2 (fun _ => (1 : ℤ)) (fun _ => rfl)
  have he := Finset.sum_sdiff (f := fun ℓ : GLeaf G.tree =>
    ((nodeSign G.sig ℓ.1 : ℤˣ) : ℤ) • (1 : ℤ)) (leavesBelow_subset_of_isDesc h.1)
  rw [hz, zero_add, ← ha, ← hb] at he
  simp only [smul_eq_mul, mul_one] at he
  exact Units.ext he.symm

/-- Every decoration has equal upper/lower values across an embedded paired tree. -/
theorem subPairedTree_value {a b : GNode G.tree} (h : IsSubPairedTree G a b)
    {V : Type*} [AddCommGroup V] {κ : GNode G.tree → V} (hκ : IsDecoration G κ) :
    κ a = κ b := by
  have ha := sum_rule G.sig κ hκ.1 a
  have hb := sum_rule G.sig κ hκ.1 b
  have hz := sum_signed_completelyPaired h.2 κ hκ.2
  have he := Finset.sum_sdiff (f := fun ℓ : GLeaf G.tree =>
    ((nodeSign G.sig ℓ.1 : ℤˣ) : ℤ) • κ ℓ.toNode) (leavesBelow_subset_of_isDesc h.1)
  rw [hz, zero_add, ← ha, ← hb] at he
  have hs : nodeSign G.sig a.1 = nodeSign G.sig b.1 := subPairedTree_sign h
  rw [← hs] at he
  rcases Int.units_eq_one_or (nodeSign G.sig a.1) with hh | hh <;>
    rw [hh] at he <;> simpa using he.symm

/-- The relative path of the lower root is a valid node in the upper subtree. -/
theorem subPairedTree_subtree {a b : GNode G.tree} (h : IsSubPairedTree G a b)
    {u : TTree} (hu : subtree (G.tree a.1.1) a.1.2 = some u) :
    ∃ q v, a.1.2 ++ q = b.1.2 ∧ subtree u q = some v := by
  obtain ⟨hj, q, hq⟩ := h.1
  have hn : b.1.2 ∈ (G.tree a.1.1).nodes := by rw [hj]; exact b.2
  obtain ⟨v, hv⟩ := (subtree_exists_iff _ _).mpr hn
  refine ⟨q, v, hq, ?_⟩
  rw [← hq, subtree_append, hu] at hv
  exact hv

end WaveTurbulence.Comb
