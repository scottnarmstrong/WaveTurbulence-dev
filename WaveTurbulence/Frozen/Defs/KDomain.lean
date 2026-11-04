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
public import WaveTurbulence.Frozen.Defs.GardenIsLoneParent
public import WaveTurbulence.Frozen.Defs.LayeredGarden

/-!
# kDomain

Wave B tier B1 (WaveB1-System.lean), source: T L674. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Kernels

variable {w : ℕ}
variable (L γ δ : ℝ) {d : ℕ}

/-- The **time domain** of the kernels: `𝔏_𝔫 < t_𝔫 < 𝔏_𝔫 + 1`, `0 < t_𝔫 < up(𝔫)`,
`t_{𝔫'} < t_𝔫` for `𝔫'` a branching child of `𝔫`, and `t_{ℓ_lo^pr} > s` at the parent of a lone
leaf. With `up ≡ t`: (timegarden) (T L674), read with `t_𝔫 < t` for every branching node (the literal
"whenever `𝔫'` is a child of `𝔫`" leaves nodes with only leaf children unconstrained; cf. (timetree)
for a tree of order 1); with `up = t` on `𝒯⁺` and `s` on `𝒯⁻`: (timecouple); with a lone leaf:
(timepairtree). -/
def kDomain (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) :
    Set (GBranch LG.garden.tree → ℝ) :=
  {τ | ∀ b, (LG.layer b.toNode : ℝ) < τ b ∧ τ b < LG.layer b.toNode + 1 ∧ 0 < τ b ∧
    τ b < up b ∧ (∀ b' : GBranch LG.garden.tree, b'.IsChildOf b → τ b' < τ b) ∧
    (LG.garden.IsLoneParent b → s < τ b)}

end Kernels
end WaveTurbulence
