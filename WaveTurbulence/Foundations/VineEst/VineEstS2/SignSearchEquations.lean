/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.SignHeavySearch

/-! # Equations for the actual same-sign predecessor search -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree
variable {w : ℕ} {tree : Fin w → TTree}

theorem signHeavySearch_none (sig : Fin w → ℤˣ) (ζ : ℤˣ) (v : GBranch tree)
    (hv : nextHeavyBranch v = none) : signHeavySearch sig ζ v = ([v],none) := by
  rw [signHeavySearch,hv]

theorem signHeavySearch_same (sig : Fin w → ℤˣ) (ζ : ℤˣ) {v u : GBranch tree}
    (hu : nextHeavyBranch v = some u) (hs : nodeSign sig u.1 = ζ) :
    signHeavySearch sig ζ v = ([v],some u) := by
  rw [signHeavySearch,hu]
  dsimp only
  rw [ite_eq_left hs]

theorem signHeavySearch_different (sig : Fin w → ℤˣ) (ζ : ℤˣ) {v u : GBranch tree}
    (hu : nextHeavyBranch v = some u) (hs : nodeSign sig u.1 ≠ ζ) :
    signHeavySearch sig ζ v = (v::(signHeavySearch sig ζ u).1,(signHeavySearch sig ζ u).2) := by
  rw [signHeavySearch,hu]
  dsimp only
  rw [ite_eq_right hs]

theorem nextHeavyBranch_desc {v u : GBranch tree} (hu : nextHeavyBranch v = some u) :
    v.toNode.IsDesc u.toNode :=
  (nextHeavyBranch_node hu).symm ▸ GBranch.isDesc_child v (heavyBranchChild v)

end WaveTurbulence.VineEstS2
