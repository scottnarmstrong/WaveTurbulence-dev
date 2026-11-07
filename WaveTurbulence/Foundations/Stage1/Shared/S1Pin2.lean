/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Pin1
import Mathlib.Tactic

/-!
# Native pins under couple erasure (CE1) and the geometry of native positions

No native position of another tree or couple lies below a leaf position of the skeleton.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ} {S : Garden w}

/-- Tree nodes are never below a leaf position. -/
theorem nu_tree (D : ReconstructionData S) (ℓ : GLeaf S.tree) (c : GBranch S.tree) (q : Path)
    (hq : q ∈ ((D.tree c).plug (nodeSign S.sig c.1) .leaf).nodes) :
    ¬ Below (inflatedPosition S D.tree ℓ.toNode) (addrExt (inflatedPosition S D.tree c.toNode) q) := by
  intro H
  have hc1 : Below (inflatedPosition S D.tree ℓ.toNode) (inflatedPosition S D.tree c.toNode) ∨
      Below (inflatedPosition S D.tree c.toNode) (inflatedPosition S D.tree ℓ.toNode) := by
    have h1 := H.2
    change (inflatedPosition S D.tree ℓ.toNode).2 <+:
      (inflatedPosition S D.tree c.toNode).2 ++ q at h1
    have hh := H.1
    change (inflatedPosition S D.tree c.toNode).1 = (inflatedPosition S D.tree ℓ.toNode).1 at hh
    rcases List.prefix_or_prefix_of_prefix h1 (List.prefix_append _ _) with h | h
    · exact Or.inl ⟨hh, h⟩
    · exact Or.inr ⟨hh.symm, h⟩
  rcases hc1 with h | h
  · exact leaf_not_above_branch S.tree ℓ c ((inflatedPosition_below_iff S D.tree ℓ.toNode c.toNode).mp h)
  · have hab := (inflatedPosition_below_iff S D.tree c.toNode ℓ.toNode).mp h
    have hne : c.toNode ≠ ℓ.toNode := by
      intro he
      have : ℓ.1 = c.1 := (congrArg (fun z : GNode S.tree => z.1) he).symm
      exact leaf_not_above_branch S.tree ℓ c (by rw [this]; exact ⟨rfl, List.prefix_refl _⟩)
    obtain ⟨i, hi⟩ := below_child_of_desc_ne c ℓ.toNode hab hne
    have he := inflatedPosition_below S D.tree (c.child i) ℓ.toNode hi
    rw [D.core_child_position] at he
    have hb2 := below_trans he H
    have h3 : (D.tree c).lonePath ++ [i] <+: q := by
      have := hb2.2
      change (inflatedPosition S D.tree c.toNode).2 ++ (D.tree c).lonePath ++ [i] <+:
        (inflatedPosition S D.tree c.toNode).2 ++ q at this
      rw [List.append_assoc] at this
      exact (List.prefix_append_right_inj _).mp this
    have := leaf_prefix_node_eq (chain_lone_mem_leaves (D.tree c) (nodeSign S.sig c.1)) hq
      ((List.prefix_append _ _).trans h3)
    subst this
    have := h3.length_le
    simp at this

/-- Nodes at the root of a different leaf are never below a leaf position. -/
theorem nu_leaf (D : ReconstructionData S) (ℓ ℓ' : GLeaf S.tree) (hne : ℓ ≠ ℓ') (r : Path) :
    ¬ Below (inflatedPosition S D.tree ℓ.toNode) (addrExt (inflatedPosition S D.tree ℓ'.toNode) r) := by
  intro H
  have hh := H.1
  have h1 := H.2
  change (inflatedPosition S D.tree ℓ.toNode).2 <+:
    (inflatedPosition S D.tree ℓ'.toNode).2 ++ r at h1
  have hh' : (inflatedPosition S D.tree ℓ'.toNode).1 = (inflatedPosition S D.tree ℓ.toNode).1 := hh
  have key : ∀ (m m' : GLeaf S.tree), Below (inflatedPosition S D.tree m.toNode)
      (inflatedPosition S D.tree m'.toNode) → m = m' := by
    intro m m' hm
    have := (inflatedPosition_below_iff S D.tree m.toNode m'.toNode).mp hm
    obtain ⟨hf, hp⟩ := this
    have hm' : m'.1.2 ∈ (S.tree m.1.1).leaves := hf ▸ m'.2
    exact Subtype.ext (Prod.ext hf.symm
      (leaf_prefix_node_eq m.2 (TTree.leaves_subset_nodes _ hm') hp))
  rcases List.prefix_or_prefix_of_prefix h1 (List.prefix_append _ _) with h | h
  · exact hne (key ℓ ℓ' ⟨hh', h⟩)
  · exact hne (key ℓ' ℓ ⟨hh'.symm, h⟩).symm

/-- Layers at ordinary native positions are unchanged across an `OutAgree` at the roots of the pair `q`. -/
theorem ce1_tree {L C : LayeredGarden w} (D : ReconstructionData S) (hS : S.IsPlain) (q : SourcePair S)
    (hA : OutAgree L C (inflatedPosition S D.tree (q.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (q.secondLeaf hS).toNode))
    (c : GBranch S.tree) (r : Path)
    (hr : r ∈ ((D.tree c).plug (nodeSign S.sig c.1) .leaf).nodes) :
    layerAt L (addrExt (inflatedPosition S D.tree c.toNode) r) =
      layerAt C (addrExt (inflatedPosition S D.tree c.toNode) r) := by
  apply hA.layer
  rintro (h | h)
  · exact nu_tree D _ c r hr ((under_iff_below_addr _ _).mp h)
  · exact nu_tree D _ c r hr ((under_iff_below_addr _ _).mp h)

theorem ce1_core {L C : LayeredGarden w} (D : ReconstructionData S) (hS : S.IsPlain) (q : SourcePair S)
    (hA : OutAgree L C (inflatedPosition S D.tree (q.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (q.secondLeaf hS).toNode)) (c : GBranch S.tree) :
    layerAt L (D.corePosition c) = layerAt C (D.corePosition c) :=
  ce1_tree D hS q hA c _ (TTree.leaves_subset_nodes _ (chain_lone_mem_leaves (D.tree c) _))

theorem pair_leaves_ne (hS : S.IsPlain) {q q' : SourcePair S} (hq : q' ≠ q) :
    (q'.firstLeaf hS ≠ q.firstLeaf hS ∧ q'.firstLeaf hS ≠ q.secondLeaf hS) ∧
    (q'.secondLeaf hS ≠ q.firstLeaf hS ∧ q'.secondLeaf hS ≠ q.secondLeaf hS) := by
  have h1 := pairOfLeaf_firstLeaf S hS q
  have h2 := pairOfLeaf_secondLeaf S hS q
  have h1' := pairOfLeaf_firstLeaf S hS q'
  have h2' := pairOfLeaf_secondLeaf S hS q'
  refine ⟨⟨fun he => hq ?_, fun he => hq ?_⟩, ⟨fun he => hq ?_, fun he => hq ?_⟩⟩
  · rw [← h1', he, h1]
  · rw [← h1', he, h2]
  · rw [← h2', he, h1]
  · rw [← h2', he, h2]

theorem ce1_couple {L C : LayeredGarden w} (D : ReconstructionData S) (hS : S.IsPlain) (q : SourcePair S)
    (hA : OutAgree L C (inflatedPosition S D.tree (q.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (q.secondLeaf hS).toNode))
    (q' : SourcePair S) (hq : q' ≠ q) (i : Fin 2) (r : Path) :
    layerAt L (addrExt (coupleRoot D hS q' i) r) = layerAt C (addrExt (coupleRoot D hS q' i) r) := by
  have hne := pair_leaves_ne hS hq
  apply hA.layer
  unfold coupleRoot
  split_ifs
  · rintro (h | h)
    · exact nu_leaf D _ _ (Ne.symm hne.1.1) r ((under_iff_below_addr _ _).mp h)
    · exact nu_leaf D _ _ (Ne.symm hne.1.2) r ((under_iff_below_addr _ _).mp h)
  · rintro (h | h)
    · exact nu_leaf D _ _ (Ne.symm hne.2.1) r ((under_iff_below_addr _ _).mp h)
    · exact nu_leaf D _ _ (Ne.symm hne.2.2) r ((under_iff_below_addr _ _).mp h)

end WaveTurbulence.Stage1
