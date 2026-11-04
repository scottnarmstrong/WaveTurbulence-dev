/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.EmbeddedCouple
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.CollapsedLeaves

/-! # Actual subtree data for an embedded collapse (TARGET L846) -/

public section

namespace WaveTurbulence.Comb
open TTree Finset

variable {w : ℕ} {tree : Fin w → TTree}

/-- The actual upper/lower subtrees and their relative node address. -/
structure CollapseData (a b : GNode tree) where
  upper : TTree
  lower : TTree
  path : Path
  sameTree : a.1.1 = b.1.1
  upper_eq : subtree (tree a.1.1) a.1.2 = some upper
  path_eq : a.1.2 ++ path = b.1.2
  lower_eq : subtree upper path = some lower

/-- Obtain collapse data from descendant containment, with no existence premise. -/
@[expose] noncomputable def collapseDataOfDesc {a b : GNode tree} (h : a.IsDesc b) : CollapseData a b where
  upper := nodeSubtree a
  lower := nodeSubtree b
  path := Classical.choose h.2
  sameTree := h.1
  upper_eq := nodeSubtree_spec a
  path_eq := Classical.choose_spec h.2
  lower_eq := by
    have hb := nodeSubtree_spec b
    rw [← h.1, ← Classical.choose_spec h.2, subtree_append, nodeSubtree_spec a] at hb
    exact hb

variable {a b : GNode tree}

/-- The non-lone leaves of the collapsed upper tree. -/
abbrev CollapseData.OtherLeaf (D : CollapseData a b) :=
  {ℓ : GLeaf (fun _ : Fin 1 => collapseAt D.upper D.path) // ℓ ≠ collapsedLone D.lower_eq}

/-- Map every non-lone collapsed leaf to its original ambient leaf. -/
@[expose] def CollapseData.leafEmbedding (D : CollapseData a b) : D.OtherLeaf ↪ GLeaf tree where
  toFun x := ⟨(a.1.1, a.1.2 ++ (collapsedOtherEquiv D.lower_eq x).1),
    (subtree_leaves_iff D.upper_eq _).mp (collapsedOtherEquiv D.lower_eq x).2.1⟩
  inj' := by
    intro x y hxy
    apply (collapsedOtherEquiv D.lower_eq).injective
    apply Subtype.ext
    have hh := congrArg (fun ℓ : GLeaf tree => ℓ.1.2) hxy
    exact List.append_cancel_left hh

/-- The image is contained in exactly the source's upper-minus-lower leaf set. -/
theorem CollapseData.leafEmbedding_mem (D : CollapseData a b) (x : D.OtherLeaf) :
    CollapseData.leafEmbedding D x ∈ a.leavesBelow \ b.leavesBelow := by
  let q := collapsedOtherEquiv D.lower_eq x
  rw [Finset.mem_sdiff]
  constructor
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, List.prefix_append _ _⟩
  · intro hb
    have hp := (Finset.mem_filter.mp hb).2.2
    change b.1.2 <+: a.1.2 ++ q.1 at hp
    rw [← D.path_eq, List.prefix_append_right_inj] at hp
    exact q.2.2 hp

/-- Every ambient leaf in the source difference has a unique non-lone preimage. -/
theorem CollapseData.leafEmbedding_surj (D : CollapseData a b)
    (ℓ : GLeaf tree) (hℓ : ℓ ∈ a.leavesBelow \ b.leavesBelow) :
    ∃ x : D.OtherLeaf, CollapseData.leafEmbedding D x = ℓ := by
  obtain ⟨ha, hb⟩ := Finset.mem_sdiff.mp hℓ
  obtain ⟨hj, q, hq⟩ := (Finset.mem_filter.mp ha).2
  have hleaf : q ∈ D.upper.leaves := by
    apply (subtree_leaves_iff D.upper_eq q).mpr
    rw [hq, hj]
    exact ℓ.2
  have hout : ¬ D.path <+: q := by
    intro hp
    apply hb
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, D.sameTree.symm.trans hj, ?_⟩
    rw [← D.path_eq, ← hq]
    exact (List.prefix_append_right_inj _).mpr hp
  refine ⟨(collapsedOtherEquiv D.lower_eq).symm ⟨q, hleaf, hout⟩, ?_⟩
  apply Subtype.ext
  change (a.1.1, a.1.2 ++ (collapsedOtherEquiv D.lower_eq
    ((collapsedOtherEquiv D.lower_eq).symm ⟨q, hleaf, hout⟩)).1) = ℓ.1
  rw [Equiv.apply_symm_apply]
  exact Prod.ext hj hq

end WaveTurbulence.Comb
