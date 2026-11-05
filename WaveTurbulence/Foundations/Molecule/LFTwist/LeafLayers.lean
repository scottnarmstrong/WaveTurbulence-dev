/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.ThresholdCriterion

/-! # Leaf layers are forced in a canonical plain garden

TARGET sublayer, L1465: paired leaves have the minimum of their two parent
layers. Roots use the ambient layer p. Thus a canonical extension of fixed
branch layers, when it exists, is unique.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Twist
variable {w : ℕ}

theorem layer_le_parentLayer (LG : LayeredGarden w) {p : ℕ}
    (hb : ∀ n, LG.layer n ≤ p) (n : GNode LG.garden.tree) :
    LG.layer n ≤ LG.parentLayer p n := by
  by_cases hn : n.1.2 = []
  · simpa only [LayeredGarden.parentLayer, hn, ite_true] using hb n
  · rw [parentLayer_nonroot LG p n hn]
    have h := LG.isLayering.1 (GNode.parent n hn) (n.1.2.getLast hn)
    rw [Mole.parent_child_eq_node n hn] at h
    exact h

/-- The exact minimum-parent formula, including root leaves. -/
theorem canonical_leaf_layer (LG : LayeredGarden w) {p : ℕ}
    (hc : LG.CanonCriterion p) (hplain : LG.garden.IsPlain) (l : GLeaf LG.garden.tree) :
    LG.layer l.toNode = min (LG.parentLayer p l.toNode)
      (LG.parentLayer p (LG.garden.pair l).toNode) := by
  have hn : LG.garden.pair l ≠ l := by
    intro h
    have hm := (LG.garden.pair_eq_iff l).mp h
    simp [hplain l] at hm
  have hclosed : LG.garden.CompletelyPaired
      (l.toNode.leavesBelow ∪ (LG.garden.pair l).toNode.leavesBelow) := by
    rw [leavesBelow_leaf, leavesBelow_leaf]
    intro m hm
    rcases Finset.mem_union.mp hm with hm | hm
    · have e := Finset.mem_singleton.mp hm
      subst m
      exact ⟨hn, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩
    · have e := Finset.mem_singleton.mp hm
      subst m
      rw [LG.garden.pair_pair]
      exact ⟨Ne.symm hn, Finset.mem_union_left _ (Finset.mem_singleton_self _)⟩
  apply Nat.le_antisymm
  · exact le_min (layer_le_parentLayer LG hc.1 _) ((LG.isLayering.2 l).trans_le
      (layer_le_parentLayer LG hc.1 _))
  · have h := hc.2 l.toNode (LG.garden.pair l).toNode (leaves_incomparable (Ne.symm hn)) hclosed
    simpa only [← LG.isLayering.2 l, max_self] using h

/-- A canonical extension is unique once every branching-node layer is fixed.
Existence from coherent reconstruction is a separate statement. -/
theorem canonical_layer_unique (G : Garden w) (f g : GNode G.tree → ℕ)
    (hf : IsLayering G f) (hg : IsLayering G g) (hplain : G.IsPlain) (p : ℕ)
    (hcf : (LayeredGarden.mk G f hf).CanonCriterion p)
    (hcg : (LayeredGarden.mk G g hg).CanonCriterion p)
    (hb : ∀ b : GBranch G.tree, f b.toNode = g b.toNode) : f = g := by
  have hp (n : GNode G.tree) :
      (LayeredGarden.mk G f hf).parentLayer p n =
        (LayeredGarden.mk G g hg).parentLayer p n := by
    by_cases hn : n.1.2 = []
    · simp only [LayeredGarden.parentLayer, hn, ite_true]
    · rw [parentLayer_nonroot ⟨G,f,hf⟩ p n hn, parentLayer_nonroot ⟨G,g,hg⟩ p n hn]
      exact hb (GNode.parent n hn)
  funext n
  obtain ⟨q,rfl⟩ := (nodePieceEquiv G.tree).surjective n
  cases q with
  | inl b => exact hb b
  | inr l =>
    exact (canonical_leaf_layer ⟨G,f,hf⟩ hcf hplain l).trans
      ((congrArg₂ min (hp l.toNode) (hp (G.pair l).toNode)).trans
        (canonical_leaf_layer ⟨G,g,hg⟩ hcg hplain l).symm)

end WaveTurbulence.LFTwist
