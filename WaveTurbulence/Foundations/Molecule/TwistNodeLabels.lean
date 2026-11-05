/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.UnitTwistMolecule

/-! # Concrete node-label transport for the unit twist

TARGET twistexplain (d): exchange k_u2 with k_u23. Both leaves in the
u23/u0 pair receive the old lower value, as required by the actual pairing.
The map is defined for arbitrary node labels; its bijectivity is restricted
to paired decorations, since leaf-pair values are redundant coordinates.
-/

public section
namespace WaveTurbulence.Twist
open TTree

/-- Actual nodes are the disjoint union of branching nodes and leaves. -/
@[expose] noncomputable def nodePieceEquiv {w : ℕ} (F : Fin w → TTree) :
    GBranch F ⊕ GLeaf F ≃ GNode F :=
  Equiv.ofBijective (Sum.elim GBranch.toNode GLeaf.toNode) (by
    constructor
    · rintro (b | l) (c | m) he
      · exact congrArg Sum.inl (Mole.branch_toNode_injective he)
      · exact (Mole.branch_toNode_ne_leaf b m he).elim
      · exact (Mole.branch_toNode_ne_leaf c l he.symm).elim
      · exact congrArg Sum.inr (Mole.leaf_toNode_injective he)
    · intro n
      rcases (TTree.mem_nodes_iff _ _).mp n.2 with hl | hb
      · exact ⟨.inr ⟨n.1,hl⟩,Subtype.ext rfl⟩
      · exact ⟨.inl ⟨n.1,hb⟩,Subtype.ext rfl⟩)

variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The actual node bijection carrying each branching node and leaf with its subtree. -/
@[expose] noncomputable def naiveNodeEquiv : GNode G.tree ≃ GNode (unitTwistGarden G P).tree :=
  (nodePieceEquiv G.tree).symm.trans
    ((Equiv.sumCongr (coreBranchEquiv G P) (coreLeafEquiv G P)).trans
      (nodePieceEquiv (unitTwistGarden G P).tree))

/-- Branching nodes follow the actual branch bijection. -/
theorem naiveNodeEquiv_branch (b : GBranch G.tree) :
    naiveNodeEquiv G P b.toNode = (coreBranchEquiv G P b).toNode := by
  change (nodePieceEquiv _) ((Equiv.sumCongr _ _)
    ((nodePieceEquiv _).symm ((nodePieceEquiv _) (.inl b)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Leaves follow the actual leaf bijection. -/
theorem naiveNodeEquiv_leaf (l : GLeaf G.tree) :
    naiveNodeEquiv G P l.toNode = (coreLeafEquiv G P l).toNode := by
  change (nodePieceEquiv _) ((Equiv.sumCongr _ _)
    ((nodePieceEquiv _).symm ((nodePieceEquiv _) (.inr l)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Exchange the lower value with the common value of its retained leaf pair. -/
@[expose] noncomputable def switchedOldLabels {E : Type*} (κ : GNode G.tree → E) (n : GNode G.tree) : E :=
  if n = P.lower.toNode then κ P.retained.toNode
  else if n = P.retained.toNode ∨ n = (G.pair P.retained).toNode then κ P.lower.toNode else κ n

/-- The concrete new node labels, with exactly the source lower/retained exchange. -/
@[expose] noncomputable def twistNodeLabels {E : Type*} (κ : GNode G.tree → E) :
    GNode (unitTwistGarden G P).tree → E := fun n => switchedOldLabels G P κ ((naiveNodeEquiv G P).symm n)

/-- Evaluate the concrete labels on the actual node transport. -/
theorem twistNodeLabels_naive {E : Type*} (κ : GNode G.tree → E) (n : GNode G.tree) :
    twistNodeLabels G P κ (naiveNodeEquiv G P n) = switchedOldLabels G P κ n := by
  simp only [twistNodeLabels,Equiv.symm_apply_apply]

/-- The lower branch receives the old retained-leaf value. -/
theorem twistNodeLabels_lower {E : Type*} (κ : GNode G.tree → E) :
    twistNodeLabels G P κ (coreBranchEquiv G P P.lower).toNode = κ P.retained.toNode := by
  rw [← naiveNodeEquiv_branch,twistNodeLabels_naive]
  simp [switchedOldLabels]

/-- Every other branching value is preserved. -/
theorem twistNodeLabels_branch {E : Type*} (κ : GNode G.tree → E) (b : GBranch G.tree) (hb : b ≠ P.lower) :
    twistNodeLabels G P κ (coreBranchEquiv G P b).toNode = κ b.toNode := by
  rw [← naiveNodeEquiv_branch,twistNodeLabels_naive]
  have hn : b.toNode ≠ P.lower.toNode := fun he => hb (Mole.branch_toNode_injective he)
  simp [switchedOldLabels,hn,Mole.branch_toNode_ne_leaf]

/-- Both exceptional leaves receive the old lower value; other leaf values are preserved. -/
theorem twistNodeLabels_leaf {E : Type*} (κ : GNode G.tree → E) (l : GLeaf G.tree) :
    twistNodeLabels G P κ (coreLeafEquiv G P l).toNode =
      if l = P.retained ∨ l = G.pair P.retained then κ P.lower.toNode else κ l.toNode := by
  rw [← naiveNodeEquiv_leaf,twistNodeLabels_naive]
  have hn : l.toNode ≠ P.lower.toNode := (Mole.branch_toNode_ne_leaf P.lower l).symm
  have h1 : l.toNode = P.retained.toNode ↔ l = P.retained :=
    ⟨fun he => Mole.leaf_toNode_injective he,fun he => congrArg GLeaf.toNode he⟩
  have h2 : l.toNode = (G.pair P.retained).toNode ↔ l = G.pair P.retained :=
    ⟨fun he => Mole.leaf_toNode_injective he,fun he => congrArg GLeaf.toNode he⟩
  simp only [switchedOldLabels,hn,ite_false,h1,h2]

end WaveTurbulence.Twist
