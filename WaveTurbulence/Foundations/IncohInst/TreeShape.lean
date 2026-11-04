/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import WaveTurbulence.Foundations.Incoh.MomentumTreeData

/-! # Forgetting the source tree to the analytic localization shape -/

public section
namespace WaveTurbulence.IncohInst

/-- The same finite ternary tree, retaining every source address. -/
@[expose] def treeShape : TTree → Incoh.LocalizationTree
  | .leaf => .leaf
  | .node l m r => .node (treeShape l) (treeShape m) (treeShape r)

@[simp] theorem treeShape_order (t : TTree) : (treeShape t).order = t.order := by
  induction t with
  | leaf => rfl
  | node l m r hl hm hr => simp only [treeShape, Incoh.LocalizationTree.order, TTree.order, hl, hm, hr]

@[simp] theorem treeShape_nodes (t : TTree) : (treeShape t).nodes = t.nodes := by
  induction t with
  | leaf => rfl
  | node l m r hl hm hr => simp only [treeShape, Incoh.LocalizationTree.nodes, TTree.nodes, hl, hm, hr]; rfl

@[simp] theorem treeShape_leaves (t : TTree) : (treeShape t).leaves = t.leaves := by
  induction t with
  | leaf => rfl
  | node l m r hl hm hr => simp only [treeShape, Incoh.LocalizationTree.leaves, TTree.leaves, hl, hm, hr]; rfl

@[simp] theorem treeShape_branching (t : TTree) : (treeShape t).branching = t.branching := by
  induction t with
  | leaf => rfl
  | node l m r hl hm hr => simp only [treeShape, Incoh.LocalizationTree.branching, TTree.branching, hl, hm, hr]; rfl

end WaveTurbulence.IncohInst
