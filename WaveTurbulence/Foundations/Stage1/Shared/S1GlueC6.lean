/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1GlueC5
import Mathlib.Tactic

/-!
# The glued layered garden (couple case)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ}

namespace GlueC
variable {LN T : LayeredGarden w} {G : Garden w} {Q : RegCpl} {a b aT bT : Fin w × Path} {p : ℕ}
  (h : GlueC LN T G Q a b aT bT p)
include h

/-- In the trivial base the leaves at the roots are paired with each other. -/
theorem base_leaf_a : a.2 ∈ (LN.garden.tree a.1).leaves := by
  have := (node_iff_of_subtree h.embN.nodeA h.embN.treeA []).2.1.2
  simpa [addrExt, RegCpl.trees] using this (by simp [RegCpl.trees, TTree.leaves])

theorem base_leaf_b : b.2 ∈ (LN.garden.tree b.1).leaves := by
  have := (node_iff_of_subtree h.embN.nodeB h.embN.treeB []).2.1.2
  simpa [addrExt, RegCpl.trees] using this (by simp [RegCpl.trees, TTree.leaves])

theorem base_pair_a : (LN.garden.pair (⟨a, h.base_leaf_a⟩ : GLeaf LN.garden.tree)).1 = b :=
  h.embN.pairs (a, b) (by simp [RegCpl.pairsAt]) (⟨a, h.base_leaf_a⟩ : GLeaf LN.garden.tree) rfl

theorem base_pair_b : (LN.garden.pair (⟨b, h.base_leaf_b⟩ : GLeaf LN.garden.tree)).1 = a := by
  have hh : LN.garden.pair (⟨a, h.base_leaf_a⟩ : GLeaf LN.garden.tree) =
      (⟨b, h.base_leaf_b⟩ : GLeaf LN.garden.tree) := Subtype.ext h.base_pair_a
  have h3 := LN.garden.pair_pair (⟨a, h.base_leaf_a⟩ : GLeaf LN.garden.tree)
  rw [hh] at h3
  exact congrArg Subtype.val h3

/-- Leaves of the base below a root are that root. -/
theorem base_leaf_under {z : Fin w × Path} (hz : z.2 ∈ (LN.garden.tree z.1).leaves) :
    (Under a z → z = a) ∧ (Under b z → z = b) := by
  constructor
  · intro hu
    obtain ⟨q, rfl⟩ := under_of_addrExt hu
    have := ((node_iff_of_subtree h.embN.nodeA h.embN.treeA q).2.1.1 hz)
    simp [RegCpl.trees, TTree.leaves] at this
    subst this; simp [addrExt]
  · intro hu
    obtain ⟨q, rfl⟩ := under_of_addrExt hu
    have := ((node_iff_of_subtree h.embN.nodeB h.embN.treeB q).2.1.1 hz)
    simp [RegCpl.trees, TTree.leaves] at this
    subst this; simp [addrExt]

theorem pair_out (ℓ : GLeaf G.tree) (hℓ : ¬ InRegion a b ℓ.1) :
    glueAt LN T a b aT bT ℓ.1 = glueAt LN T a b aT bT (G.pair ℓ).1 := by
  have hl' : ℓ.1.2 ∈ (LN.garden.tree ℓ.1.1).leaves := (h.leaf ℓ.1 hℓ).mp ℓ.2
  let ℓ' : GLeaf LN.garden.tree := ⟨ℓ.1, hl'⟩
  have hp := h.pair ℓ ℓ' hℓ rfl
  have hout : ¬ InRegion a b (LN.garden.pair ℓ').1 := by
    intro hin
    have hleaf := (LN.garden.pair ℓ').2
    rcases hin with hin | hin
    · have e : (LN.garden.pair ℓ').1 = a := (h.base_leaf_under hleaf).1 hin
      have : LN.garden.pair ℓ' = (⟨a, h.base_leaf_a⟩ : GLeaf LN.garden.tree) := Subtype.ext e
      have h2 : ℓ' = (⟨b, h.base_leaf_b⟩ : GLeaf LN.garden.tree) := by
        have := congrArg LN.garden.pair this
        rw [LN.garden.pair_pair] at this
        rw [this]; exact Subtype.ext h.base_pair_a
      exact hℓ (Or.inr (by have := congrArg Subtype.val h2; simp only [ℓ'] at this; rw [this]; exact under_refl b))
    · have e : (LN.garden.pair ℓ').1 = b := (h.base_leaf_under hleaf).2 hin
      have : LN.garden.pair ℓ' = (⟨b, h.base_leaf_b⟩ : GLeaf LN.garden.tree) := Subtype.ext e
      have h2 : ℓ' = (⟨a, h.base_leaf_a⟩ : GLeaf LN.garden.tree) := by
        have := congrArg LN.garden.pair this
        rw [LN.garden.pair_pair] at this
        rw [this]; exact Subtype.ext h.base_pair_b
      exact hℓ (Or.inl (by have := congrArg Subtype.val h2; simp only [ℓ'] at this; rw [this]; exact under_refl a))
  rw [glueAt_out _ _ _ _ _ _ hℓ, hp, glueAt_out _ _ _ _ _ _ hout]
  have e1 := layerAt_node LN ℓ'.toNode
  have e2 := layerAt_node LN (LN.garden.pair ℓ').toNode
  have e3 := LN.isLayering.2 ℓ'
  exact e1.trans (e3.trans e2.symm)

theorem isLayering : IsLayering G (fun n => glueAt LN T a b aT bT n.1) := by
  refine ⟨fun c i => h.child_le c i, fun ℓ => ?_⟩
  by_cases hℓ : InRegion a b ℓ.1
  · exact h.pair_in_region ℓ hℓ
  · exact h.pair_out ℓ hℓ

/-- The glued layered garden. -/
@[expose] noncomputable def glued : LayeredGarden w :=
  ⟨G, fun n => glueAt LN T a b aT bT n.1, h.isLayering⟩

end GlueC
end WaveTurbulence.Stage1
