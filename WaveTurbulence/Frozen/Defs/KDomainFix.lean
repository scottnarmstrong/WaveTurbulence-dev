/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GBranch
public import WaveTurbulence.Frozen.Defs.GBranchIsChildOf
public import WaveTurbulence.Frozen.Defs.GBranchToNode
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.LayeredGarden

/-!
# kDomainFix

Wave B tier B1 (WaveB1-Flower.lean), source: T L2331. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section General

variable {w : ℕ}

/-- The **time domain with designated nodes**:
- every free node has `𝔏_𝔫 < t_𝔫 < 𝔏_𝔫 + 1`, `0 < t_𝔫 < up(𝔫)`;
- `t_{𝔫'} < t_𝔫` for a branching child `𝔫'` of `𝔫` whenever at least one of the two is free.

The constraints that only involve designated nodes are dropped. Their times are prescribed, and a Dirac
factor `δ(t_𝔫 − s)` sits on the boundary `t_𝔫 = t_{𝔫'}` (T L2331). With the flower parents as the
designated nodes and no lone leaves, this is `kDomain` (bridge `kDomainFix_flowerParents`, probes). -/
def kDomainFix (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) : Set (GBranch LG.garden.tree → ℝ) :=
  {τ | ∀ b, (fix b = none → (LG.layer b.toNode : ℝ) < τ b ∧ τ b < LG.layer b.toNode + 1 ∧
      0 < τ b ∧ τ b < up b) ∧
    ∀ b' : GBranch LG.garden.tree, b'.IsChildOf b → (fix b' = none ∨ fix b = none) → τ b' < τ b}

end General
end WaveTurbulence
