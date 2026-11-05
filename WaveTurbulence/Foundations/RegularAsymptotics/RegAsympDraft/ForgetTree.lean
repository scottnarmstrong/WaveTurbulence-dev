/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WaveB.RegularHeldOut
public import WaveTurbulence.Foundations.Incoh.LocalizationTree

/-! # The exact unsigned shape used by the proved leaf-localization helpers -/

@[expose] public section
namespace WaveTurbulence.RegAsymp

/-- Forget source signs while retaining the complete ternary shape. -/
def localizationTree : TTree → Incoh.LocalizationTree
  | .leaf => .leaf
  | .node l m r => .node (localizationTree l) (localizationTree m) (localizationTree r)

@[simp] theorem localizationTree_order (t : TTree) : (localizationTree t).order = t.order := by
  induction t with
  | leaf => rfl
  | node l m r hl hm hr => simp only [localizationTree,Incoh.LocalizationTree.order,TTree.order,hl,hm,hr]

@[simp] theorem localizationTree_nodes (t : TTree) : (localizationTree t).nodes = t.nodes := by
  induction t with
  | leaf => rfl
  | node l m r hl hm hr =>
    simp only [localizationTree,Incoh.LocalizationTree.nodes,TTree.nodes,hl,hm,hr]
    rfl

@[simp] theorem localizationTree_leaves (t : TTree) : (localizationTree t).leaves = t.leaves := by
  induction t with
  | leaf => rfl
  | node l m r hl hm hr =>
    simp only [localizationTree,Incoh.LocalizationTree.leaves,TTree.leaves,hl,hm,hr]
    rfl

@[simp] theorem localizationTree_branching (t : TTree) : (localizationTree t).branching = t.branching := by
  induction t with
  | leaf => rfl
  | node l m r hl hm hr =>
    simp only [localizationTree,Incoh.LocalizationTree.branching,TTree.branching,hl,hm,hr]
    rfl

end WaveTurbulence.RegAsymp
