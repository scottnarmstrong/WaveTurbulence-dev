/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.CLSignedBoundary
import Mathlib.Tactic

/-! # The actual CL retained leaves are closed under the old pairing -/

public section
namespace WaveTurbulence.Mole
open TTree

private theorem retained_complement_logic {A B C D E : Prop}
    (h : E ↔ A ∧ ¬ B ∧ ¬ C ∧ ¬ D) : (¬ A ∨ B ∨ C ∨ D) ↔ ¬ E := by tauto

variable {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b)
variable (e k : Fin 3) (he : e.succ ∉ internalPositions G S a) (he1 : e ≠ 1)

theorem forall_excluded_children_iff (hk1 : k ≠ 1) (P : Fin 3 → Prop) :
    (∀ i : Fin 3, i ≠ k → ¬ P i) ↔ ¬ P 1 ∧ ¬ P (otherOuterChild k) := by
  have hc : ∀ k : Fin 3, k ≠ 1 → ∀ i : Fin 3,
      i ≠ k ↔ i = 1 ∨ i = otherOuterChild k := by decide
  constructor
  · intro h
    exact ⟨h 1 hk1.symm,h _ (otherOuterChild_ne k hk1)⟩
  · rintro ⟨h1,h2⟩ i hi
    rcases (hc k hk1 i).mp hi with rfl | rfl
    · exact h1
    · exact h2

/-- The transported leaves are precisely the complement of the removed
CL realization leaves, with the source pairing retained literally. -/
theorem clSignedBoundary_retained_iff (hk1 : k ≠ 1)
    (ha : ∀ i : Fin 3, i.succ ∈ internalPositions G S a ↔ i ≠ e)
    (hb : ∀ i : Fin 3, i.succ ∈ internalPositions G S b ↔ i = k) (l : GLeaf G.tree) :
    IsSpliceRetainedLeaf (clSignedBoundaryRoots hB hCL e k he he1) l ↔ ¬ IsInternalLeaf G S l := by
  classical
  have hL := (cl_leaf_realization_iff G hB hCL l).trans
    (cl_pruned_region_explicit G ha hb l.toNode)
  rw [forall_excluded_children_iff k hk1] at hL
  unfold IsSpliceRetainedLeaf
  rw [clSignedBoundary_descendant_union hB hCL e k he he1]
  exact retained_complement_logic hL

theorem clSignedBoundary_pair_closed (hk1 : k ≠ 1)
    (ha : ∀ i : Fin 3, i.succ ∈ internalPositions G S a ↔ i ≠ e)
    (hb : ∀ i : Fin 3, i.succ ∈ internalPositions G S b ↔ i = k)
    (l : GLeaf G.tree) (hl : IsSpliceRetainedLeaf (clSignedBoundaryRoots hB hCL e k he he1) l) :
    IsSpliceRetainedLeaf (clSignedBoundaryRoots hB hCL e k he he1) (G.pair l) := by
  rw [clSignedBoundary_retained_iff hB hCL e k he he1 hk1 ha hb] at hl ⊢
  exact fun hp => hl ((internal_leaf_pair_iff G S l).mp hp)

end WaveTurbulence.Mole
