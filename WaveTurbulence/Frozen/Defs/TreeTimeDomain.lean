/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GBranch
public import WaveTurbulence.Frozen.Defs.GBranchIsChildOf
public import WaveTurbulence.Frozen.Defs.Single
public import WaveTurbulence.Frozen.Defs.TTree

/-!
# treeTimeDomain

Wave B tier B1 (WaveB1-System.lean), source: T L714. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Duhamel

variable (L γ δ : ℝ) {d : ℕ}

/-- The duration domain (timetree) `{p < t_{𝔫'} < t_𝔫 < t}` (T L714), read with `p < t_𝔫 < t` for all
branching nodes. -/
def treeTimeDomain (T : TTree) (p t : ℝ) : Set (GBranch (single T) → ℝ) :=
  {τ | ∀ b, p < τ b ∧ τ b < t ∧ ∀ b' : GBranch (single T), b'.IsChildOf b → τ b' < τ b}

end Duhamel
end WaveTurbulence
