/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.SideLeafBudget
public import WaveTurbulence.Foundations.VineEst.VineEstS2.SourceSignIntervals

/-! # The actual heavy-child successor and its finite-depth termination measure -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree
variable {w : ℕ} {tree : Fin w → TTree}

noncomputable def nextHeavyBranch (v : GBranch tree) : Option (GBranch tree) := by
  classical
  let x := v.child (heavyBranchChild v)
  exact if hx : x.1.2 ∈ (tree x.1.1).branching then some ⟨x.1,hx⟩ else none

theorem nextHeavyBranch_node {v u : GBranch tree} (hu : nextHeavyBranch v = some u) :
    u.toNode = v.child (heavyBranchChild v) := by
  classical
  unfold nextHeavyBranch at hu
  dsimp only at hu
  split at hu
  · have he := Option.some.inj hu
    exact congrArg GBranch.toNode he.symm
  · contradiction

theorem nextHeavyBranch_depth {v u : GBranch tree} (hu : nextHeavyBranch v = some u) :
    u.1.2.length = v.1.2.length+1 := by
  have he := congrArg (fun x : GNode tree => x.1.2) (nextHeavyBranch_node hu)
  change u.1.2 = v.1.2++[heavyBranchChild v] at he
  rw [he,List.length_append,List.length_singleton]

noncomputable def branchDepthBound (tree : Fin w → TTree) : ℕ :=
  Finset.univ.sup (fun v : GBranch tree => v.1.2.length)

theorem branch_depth_le (v : GBranch tree) : v.1.2.length ≤ branchDepthBound tree :=
  Finset.le_sup (f := fun v : GBranch tree => v.1.2.length) (Finset.mem_univ v)

theorem nextHeavyBranch_measure_lt {v u : GBranch tree} (hu : nextHeavyBranch v = some u) :
    branchDepthBound tree-u.1.2.length < branchDepthBound tree-v.1.2.length := by
  have he := nextHeavyBranch_depth hu
  have hb := branch_depth_le u
  omega

end WaveTurbulence.VineEstS2
