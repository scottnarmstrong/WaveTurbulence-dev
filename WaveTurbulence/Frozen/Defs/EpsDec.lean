/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.EpsCoef
public import WaveTurbulence.Frozen.Defs.GBranch
public import WaveTurbulence.Frozen.Defs.GBranchChild
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.InstFintypeGBranch

/-!
# epsDec

Wave B tier B1 (WaveB1-Core.lean), source: T (defepscoef); T (defcoef0). Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

section Decorations

variable {w : ℕ} (G : Garden w)

/-- `ε_ℐ = ∏_{𝔫 ∈ 𝒩} ε_{k_{𝔫₁} k_{𝔫₂} k_{𝔫₃}}` (T (defepscoef)), with `ε = epsCoef` (T (defcoef0))
evaluated on the integer labels of a decoration (for
coset decorations `k + z/L` this gives the same value, `z ↦ k + z/L` being injective). -/
def epsDec {d : ℕ} (κ : GNode G.tree → (Fin d → ℤ)) : ℝ :=
  ∏ b : GBranch G.tree, epsCoef (κ (b.child 0)) (κ (b.child 1)) (κ (b.child 2))

end Decorations
end WaveTurbulence
