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
public import WaveTurbulence.Frozen.Defs.TTree

/-!
# IsBranchConsistent

Wave B tier B1 (WaveB1-System.lean), source: (file) WAVE-B §2.3; T L545–L564; T Def `defcm`. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Duhamel

variable (L γ δ : ℝ) {d : ℕ}

/-- Branch-consistent labels on a forest: `κ_𝔫 = κ_{𝔫₁} - κ_{𝔫₂} + κ_{𝔫₃}`. -/
def IsBranchConsistent {w : ℕ} {tree : Fin w → TTree} {V : Type*} [AddCommGroup V]
    (κ : GNode tree → V) : Prop :=
  ∀ b : GBranch tree, κ b.toNode = κ (b.child 0) - κ (b.child 1) + κ (b.child 2)

end Duhamel
end WaveTurbulence
