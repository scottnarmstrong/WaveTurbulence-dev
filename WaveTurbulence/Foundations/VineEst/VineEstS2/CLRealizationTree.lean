/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CutPaths
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLRegionSupport
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.EmbeddedCouple

/-! # The actual CL realization as a finite ternary tree with three boundary leaves -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- The exact realization characterization, stated with the literal chosen
slots so consumers do not unfold the imported geometric-data constructor. -/
theorem cl_realization_iff (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (v : GNode G.tree) : Mole.InIncidenceRealization G U v ↔
    a.toNode.IsDesc v ∧ ¬ (a.child R.excluded).IsDesc v ∧
      ¬ (b.child R.positive).IsDesc v ∧ ¬ (b.child R.negative).IsDesc v := by
  have hdeg := hU
  rw [Mole.cl_node_realization_iff G hdeg R.parentPattern,
    Mole.cl_pruned_region_explicit G R.upper R.lower]
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  constructor
  · intro h
    exact ⟨h R.positive ((R.lower_excluded _).mpr (Or.inl rfl)),
      h R.negative ((R.lower_excluded _).mpr (Or.inr rfl))⟩
  · rintro ⟨hp,hn⟩ i hi
    rcases (R.lower_excluded i).mp hi with rfl | rfl
    · exact hp
    · exact hn

noncomputable def clCutPaths (R : CLRegionData G U a b) : Finset Path :=
  {(a.child R.excluded).1.2,(b.child R.positive).1.2,(b.child R.negative).1.2}

noncomputable def clRealizationTree (R : CLRegionData G U a b) : TTree :=
  cropTree (Comb.nodeSubtree a.toNode) (avoidCutPaths a.1.2 (clCutPaths R))

/-- The cropped tree's branching nodes are mapped to their literal original
addresses. All three boundary subtrees have been cut at their actual roots. -/
noncomputable def clTreeBranch (R : CLRegionData G U a b)
    (p : ↥(clRealizationTree R).branching) : GBranch G.tree :=
  ⟨(a.1.1,a.1.2++p.1),(Comb.subtree_branching_iff (Comb.nodeSubtree_spec a.toNode) p.1).mp
    (cropTree_branching_subset _ _ p.2)⟩

theorem clTreeBranch_injective (R : CLRegionData G U a b) : Function.Injective (clTreeBranch R) := by
  intro p q he
  have hp := congrArg (fun v : GBranch G.tree => v.1.2) he
  exact Subtype.ext (List.append_cancel_left hp)

theorem clTreeBranch_mem (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (p : ↥(clRealizationTree R).branching) : clTreeBranch R p ∈ U := by
  have hp := (cropTree_avoidCuts_branching_iff (Comb.nodeSubtree a.toNode) a.1.2 (clCutPaths R) p.1).mp p.2
  apply (Mole.branch_incidence_realization_iff G U _).mp
  apply (cl_realization_iff hU R _).mpr
  refine ⟨⟨rfl,⟨p.1,rfl⟩⟩,?_,?_,?_⟩
  · intro he
    apply hp.2 (a.child R.excluded).1.2 (by simp [clCutPaths])
    change _ ∧ (a.child R.excluded).1.2.IsPrefix (a.1.2++p.1) at he
    exact he.2
  · intro he
    apply hp.2 (b.child R.positive).1.2 (by simp [clCutPaths])
    change _ ∧ (b.child R.positive).1.2.IsPrefix (a.1.2++p.1) at he
    exact he.2
  · intro he
    apply hp.2 (b.child R.negative).1.2 (by simp [clCutPaths])
    change _ ∧ (b.child R.negative).1.2.IsPrefix (a.1.2++p.1) at he
    exact he.2

end WaveTurbulence.VineEstS2
