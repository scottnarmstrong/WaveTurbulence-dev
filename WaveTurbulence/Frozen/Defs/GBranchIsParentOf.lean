/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GBranch
public import WaveTurbulence.Frozen.Defs.GLeaf
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreeBranching
public import WaveTurbulence.Frozen.Defs.TTreeLeaves
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# GBranch.IsParentOf

Wave B tier B1 (WaveB1-System.lean), source: (file) WAVE-B §2.3; T L545–L564; T Def `defcm`. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Kernels

variable {w : ℕ}

/-- `b` is the parent of the leaf `ℓ`. -/
def GBranch.IsParentOf {w : ℕ} {tree : Fin w → TTree} (b : GBranch tree) (ℓ : GLeaf tree) : Prop :=
  ℓ.1.1 = b.1.1 ∧ ∃ i : Fin 3, ℓ.1.2 = b.1.2 ++ [i]

end Kernels
end WaveTurbulence
