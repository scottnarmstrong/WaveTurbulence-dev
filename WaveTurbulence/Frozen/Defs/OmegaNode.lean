/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GBranch
public import WaveTurbulence.Frozen.Defs.GBranchChild
public import WaveTurbulence.Frozen.Defs.GBranchToNode
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.ResFactor

/-!
# omegaNode

Wave B tier B1 (WaveB1-Core.lean), source: T (defomega). Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

section Decorations

variable {w : ℕ} (G : Garden w)

/-- `Ω_𝔫` of a branching node for a vector decoration `k` (T (defomega)). -/
noncomputable def omegaNode {d : ℕ} (k : GNode G.tree → Mom d) (b : GBranch G.tree) : ℝ :=
  resFactor (k (b.child 0)) (k (b.child 1)) (k (b.child 2)) (k b.toNode)

end Decorations
end WaveTurbulence
