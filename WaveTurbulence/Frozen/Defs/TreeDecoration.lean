/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.GNodeRoot
public import WaveTurbulence.Frozen.Defs.IsBranchConsistent
public import WaveTurbulence.Frozen.Defs.Single
public import WaveTurbulence.Frozen.Defs.TTree

/-!
# TreeDecoration

Wave B tier B1 (WaveB1-System.lean), source: T Def `defdec`. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Duhamel

variable (L γ δ : ℝ) {d : ℕ}

/-- The `n`-decorations of a tree (T Def `defdec`, first paragraph). -/
def TreeDecoration (T : TTree) (d : ℕ) (n : Fin d → ℤ) : Type :=
  {κ : GNode (single T) → (Fin d → ℤ) // IsBranchConsistent κ ∧ κ (GNode.root _ 0) = n}

end Duhamel
end WaveTurbulence
