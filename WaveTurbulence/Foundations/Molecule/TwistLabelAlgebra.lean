/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistDecorations

/-! # Inverting the redundant paired-leaf label exchange

TARGET twistexplain (d): the exchange is involutive on paired labels.
It is deliberately not asserted to be invertible on arbitrary node
functions with inconsistent values on the two exceptional leaves.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The old-coordinate value switch reverses itself on labels agreeing on the exceptional pair. -/
theorem switchedOldLabels_involutive {E : Type*} (κ : GNode G.tree → E)
    (hpair : κ P.retained.toNode = κ (G.pair P.retained).toNode) (n : GNode G.tree) :
    switchedOldLabels G P (switchedOldLabels G P κ) n = κ n := by
  classical
  have hb0 := Mole.branch_toNode_ne_leaf P.lower P.retained
  have hb1 := Mole.branch_toNode_ne_leaf P.lower (G.pair P.retained)
  have h0b := hb0.symm
  have h1b := hb1.symm
  have h01 : P.retained.toNode ≠ (G.pair P.retained).toNode := by
    intro he
    exact (Garden.pair_ne_of_unmarked P.unmarked).symm (Mole.leaf_toNode_injective he)
  have h10 := h01.symm
  by_cases hn : n = P.lower.toNode <;> by_cases h0 : n = P.retained.toNode <;>
    by_cases h1 : n = (G.pair P.retained).toNode
  all_goals simp_all [switchedOldLabels]

/-- The inverse label recipe pulls back to old node coordinates and applies the same value switch. -/
@[expose] noncomputable def untwistNodeLabels {E : Type*}
    (η : GNode (unitTwistGarden G P).tree → E) : GNode G.tree → E :=
  switchedOldLabels G P (fun n => η (naiveNodeEquiv G P n))

/-- Pullback of paired new labels is paired in the old leaf coordinates. -/
theorem pullback_labels_paired {E : Type*} (η : GNode (unitTwistGarden G P).tree → E)
    (hη : ∀ l : GLeaf (unitTwistGarden G P).tree, η l.toNode = η ((unitTwistGarden G P).pair l).toNode)
    (l : GLeaf G.tree) :
    η (naiveNodeEquiv G P l.toNode) = η (naiveNodeEquiv G P (G.pair l).toNode) := by
  have hh := hη (coreLeafEquiv G P l)
  rw [unitTwistGarden_pair] at hh
  exact (congrArg η (naiveNodeEquiv_leaf G P l)).trans
    (hh.trans (congrArg η (naiveNodeEquiv_leaf G P (G.pair l))).symm)

/-- Inverse-after-forward on paired labels. -/
theorem untwist_twistNodeLabels {E : Type*} (κ : GNode G.tree → E)
    (hpair : κ P.retained.toNode = κ (G.pair P.retained).toNode) :
    untwistNodeLabels G P (twistNodeLabels G P κ) = κ := by
  have he : (fun n => twistNodeLabels G P κ (naiveNodeEquiv G P n)) = switchedOldLabels G P κ :=
    funext (twistNodeLabels_naive G P κ)
  unfold untwistNodeLabels
  rw [he]
  exact funext (switchedOldLabels_involutive G P κ hpair)

/-- Forward-after-inverse on paired labels in the actual twisted garden. -/
theorem twist_untwistNodeLabels {E : Type*} (η : GNode (unitTwistGarden G P).tree → E)
    (hη : ∀ l : GLeaf (unitTwistGarden G P).tree, η l.toNode = η ((unitTwistGarden G P).pair l).toNode) :
    twistNodeLabels G P (untwistNodeLabels G P η) = η := by
  funext n
  unfold twistNodeLabels untwistNodeLabels
  rw [switchedOldLabels_involutive G P _ (pullback_labels_paired G P η hη P.retained)]
  rw [Equiv.apply_symm_apply]

/-- Switching old-coordinate values preserves all old leaf-pair equations. -/
theorem switchedOldLabels_paired {E : Type*} (κ : GNode G.tree → E)
    (hκ : ∀ l : GLeaf G.tree, κ l.toNode = κ (G.pair l).toNode) (l : GLeaf G.tree) :
    switchedOldLabels G P κ l.toNode = switchedOldLabels G P κ (G.pair l).toNode := by
  have hh := twistNodeLabels_leaf_pairs G P κ hκ (coreLeafEquiv G P l)
  rw [unitTwistGarden_pair] at hh
  have h0 := twistNodeLabels_naive G P κ l.toNode
  have h1 := twistNodeLabels_naive G P κ (G.pair l).toNode
  rw [naiveNodeEquiv_leaf] at h0 h1
  exact h0.symm.trans (hh.trans h1)

/-- The inverse recipe preserves actual leaf-pair equality. -/
theorem untwistNodeLabels_paired {E : Type*} (η : GNode (unitTwistGarden G P).tree → E)
    (hη : ∀ l : GLeaf (unitTwistGarden G P).tree, η l.toNode = η ((unitTwistGarden G P).pair l).toNode)
    (l : GLeaf G.tree) :
    untwistNodeLabels G P η l.toNode = untwistNodeLabels G P η (G.pair l).toNode :=
  switchedOldLabels_paired G P _ (pullback_labels_paired G P η hη) l

end WaveTurbulence.Twist
