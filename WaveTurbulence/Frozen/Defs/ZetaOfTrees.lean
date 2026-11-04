/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreeBranching
public import WaveTurbulence.Frozen.Defs.TTreePath
public import WaveTurbulence.Frozen.Defs.TTreePathSign

/-!
# zetaOfTrees

Wave B tier B2 (WaveB2-Regular.lean), source: (file) WAVE-B v2 §2.7; L826–L829; L848–L850. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- `ζ(𝒢) = ∏_{𝔫 ∈ 𝒩} (i ζ_𝔫)` over the branching nodes of trees `T j` with root signs `σ j`. -/
noncomputable def zetaOfTrees {w : ℕ} (σ : Fin w → ℤˣ) (T : Fin w → TTree) : ℂ :=
  ∏ j, ∏ p ∈ (T j).branching, (Complex.I * (((pathSign (σ j) p : ℤˣ) : ℤ) : ℂ))

end WaveTurbulence
