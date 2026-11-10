/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.EmbeddedCriteria

/-! # Exact signed side-subtree expansion for a predecessor relation -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree

noncomputable def sideLeaves {w : ℕ} {tree : Fin w → TTree}
    (v : GBranch tree) (i : Fin 3) : Finset (GLeaf tree) :=
  v.toNode.leavesBelow \ (v.child i).leavesBelow

end WaveTurbulence.VineEstS2
