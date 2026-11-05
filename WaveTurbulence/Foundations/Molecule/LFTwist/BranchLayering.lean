/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.LeafLayers

/-! # Extending branch pre-layerings by the source minimum-parent rule

This constructs an actual layering, without asserting canonicity. Canonicity
of an induced skeleton requires the coherent-collapse argument separately.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Twist
variable {w : ℕ}

/-- TARGET deflayer restricted to actual branching nodes. -/
@[expose] def IsBranchPrelayering (G : Garden w) (f : GBranch G.tree → ℕ) : Prop :=
  ∀ (b c : GBranch G.tree) (i : Fin 3), c.toNode = b.child i → f c ≤ f b

/-- A node's parent branch value, with the ambient top value at roots. -/
@[expose] noncomputable def branchParentValue (G : Garden w) (f : GBranch G.tree → ℕ)
    (p : ℕ) (n : GNode G.tree) : ℕ :=
  if hn : n.1.2 = [] then p else f (GNode.parent n hn)

/-- The source extension keeps branch values and assigns the minimum to both paired leaves. -/
@[expose] noncomputable def extendBranchLayers (G : Garden w) (f : GBranch G.tree → ℕ)
    (p : ℕ) (n : GNode G.tree) : ℕ :=
  Sum.elim f (fun l => min (branchParentValue G f p l.toNode)
    (branchParentValue G f p (G.pair l).toNode)) ((nodePieceEquiv G.tree).symm n)

theorem extendBranchLayers_branch (G : Garden w) (f : GBranch G.tree → ℕ)
    (p : ℕ) (b : GBranch G.tree) : extendBranchLayers G f p b.toNode = f b := by
  change Sum.elim _ _ ((nodePieceEquiv G.tree).symm ((nodePieceEquiv G.tree) (.inl b))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem extendBranchLayers_leaf (G : Garden w) (f : GBranch G.tree → ℕ)
    (p : ℕ) (l : GLeaf G.tree) : extendBranchLayers G f p l.toNode =
      min (branchParentValue G f p l.toNode) (branchParentValue G f p (G.pair l).toNode) := by
  change Sum.elim _ _ ((nodePieceEquiv G.tree).symm ((nodePieceEquiv G.tree) (.inr l))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem branchParentValue_child (G : Garden w) (f : GBranch G.tree → ℕ)
    (p : ℕ) (b : GBranch G.tree) (i : Fin 3) : branchParentValue G f p (b.child i) = f b := by
  have hn : (b.child i).1.2 ≠ [] := by simp [GBranch.child]
  rw [branchParentValue, dite_eq_right hn, parent_eq_of_child hn rfl]

/-- Every monotone branch pre-layering has the specified actual layered extension. -/
theorem extendBranchLayers_isLayering (G : Garden w) (f : GBranch G.tree → ℕ)
    (p : ℕ) (hf : IsBranchPrelayering G f) : IsLayering G (extendBranchLayers G f p) := by
  constructor
  · intro b i
    rw [extendBranchLayers_branch]
    obtain ⟨q,hq⟩ := (nodePieceEquiv G.tree).surjective (b.child i)
    cases q with
    | inl c =>
      change c.toNode = b.child i at hq
      rw [← hq, extendBranchLayers_branch]
      exact hf b c i hq
    | inr l =>
      change l.toNode = b.child i at hq
      rw [← hq, extendBranchLayers_leaf]
      exact (min_le_left _ _).trans_eq (by rw [hq, branchParentValue_child])
  · intro l
    rw [extendBranchLayers_leaf, extendBranchLayers_leaf, G.pair_pair, min_comm]

/-- An explicit layered garden realizing the branch extension. -/
@[expose] noncomputable def branchLayeredGarden (G : Garden w) (f : GBranch G.tree → ℕ)
    (p : ℕ) (hf : IsBranchPrelayering G f) : LayeredGarden w :=
  ⟨G, extendBranchLayers G f p, extendBranchLayers_isLayering G f p hf⟩

/-- The constructed extension respects the ambient top-layer bound. -/
theorem extendBranchLayers_le (G : Garden w) (f : GBranch G.tree → ℕ)
    (p : ℕ) (hf : ∀ b, f b ≤ p) (n : GNode G.tree) :
    extendBranchLayers G f p n ≤ p := by
  obtain ⟨q,rfl⟩ := (nodePieceEquiv G.tree).surjective n
  cases q with
  | inl b =>
    change extendBranchLayers G f p b.toNode ≤ p
    rw [extendBranchLayers_branch]
    exact hf b
  | inr l =>
    change extendBranchLayers G f p l.toNode ≤ p
    rw [extendBranchLayers_leaf]
    apply (min_le_left _ _).trans
    unfold branchParentValue
    split
    · exact le_rfl
    · exact hf _

/-- Parent values computed solely from branch layers are the actual parent layers. -/
theorem branchParentValue_eq_parentLayer (LG : LayeredGarden w) (p : ℕ)
    (n : GNode LG.garden.tree) :
    branchParentValue LG.garden (fun b => LG.layer b.toNode) p n = LG.parentLayer p n := by
  by_cases hn : n.1.2 = []
  · simp only [branchParentValue, LayeredGarden.parentLayer, hn, dite_eq_left, ite_true]
  · rw [branchParentValue, dite_eq_right hn, parentLayer_nonroot LG p n hn]

/-- The extended layering computes parent layers using the input branch values. -/
theorem branchParentValue_eq_extension_parentLayer (G : Garden w)
    (f : GBranch G.tree → ℕ) (p : ℕ) (hf : IsBranchPrelayering G f)
    (n : GNode G.tree) :
    branchParentValue G f p n = (branchLayeredGarden G f p hf).parentLayer p n := by
  by_cases hn : n.1.2 = []
  · simp only [branchParentValue, LayeredGarden.parentLayer, hn, dite_eq_left, ite_true]
  · rw [branchParentValue, dite_eq_right hn,
      parentLayer_nonroot (branchLayeredGarden G f p hf) p n hn]
    exact (extendBranchLayers_branch G f p (GNode.parent n hn)).symm

/-- The source minimum-parent extension recovers any existing canonical plain layering. -/
theorem extendBranchLayers_eq_canonical (LG : LayeredGarden w) (p : ℕ)
    (hc : LG.CanonCriterion p) (hplain : LG.garden.IsPlain) :
    extendBranchLayers LG.garden (fun b => LG.layer b.toNode) p = LG.layer := by
  funext n
  obtain ⟨q,rfl⟩ := (nodePieceEquiv LG.garden.tree).surjective n
  cases q with
  | inl b => exact extendBranchLayers_branch _ _ _ _
  | inr l =>
    change extendBranchLayers LG.garden (fun b => LG.layer b.toNode) p l.toNode = LG.layer l.toNode
    rw [extendBranchLayers_leaf, branchParentValue_eq_parentLayer,
      branchParentValue_eq_parentLayer]
    exact (canonical_leaf_layer LG hc hplain l).symm

end WaveTurbulence.LFTwist
