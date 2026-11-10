/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLPredecessorRows
public import WaveTurbulence.Foundations.VineEst.VineEstS2.SourceBranchCost
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Prod.Lex.Basic

/-! # Transport of actual interior branches to the cropped tree -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

noncomputable def clForestBranchEquiv (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) :
    GBranch (CLTreeForest R) ≃ ↥U :=
  (singleTreeBranchEquiv (clRealizationTree R)).trans (clTreeBranchEquiv hU R)

noncomputable def clInteriorCrop (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (v : ↥(clInteriorBranches R)) : GBranch (CLTreeForest R) :=
  (clForestBranchEquiv hU R).symm ⟨v.1,(Finset.mem_erase.mp v.2).2⟩

theorem clInteriorCrop_injective (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) :
    Function.Injective (clInteriorCrop hU R) := by
  intro v u he
  have ht := (clForestBranchEquiv hU R).symm.injective he
  exact Subtype.ext (congrArg (fun q : ↥U => q.1) ht)

theorem clForestBranch_node (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (v : GBranch (CLTreeForest R)) :
    clTreeNode R v.toNode = ((clForestBranchEquiv hU R) v).1.toNode := clTreeNode_branch R v

theorem clInteriorCrop_node (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (v : ↥(clInteriorBranches R)) : clTreeNode R (clInteriorCrop hU R v).toNode = v.1.toNode := by
  rw [clForestBranch_node]
  exact congrArg (fun q : ↥U => q.1.toNode) ((clForestBranchEquiv hU R).apply_symm_apply _)

theorem clInteriorCrop_depth (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (v : ↥(clInteriorBranches R)) :
    v.1.1.2.length = a.1.2.length+(clInteriorCrop hU R v).1.2.length := by
  have hp := congrArg (fun x : GNode G.tree => x.1.2) (clInteriorCrop_node hU R v)
  change a.1.2++(clInteriorCrop hU R v).1.2 = v.1.1.2 at hp
  rw [← hp,List.length_append]

end WaveTurbulence.VineEstS2
