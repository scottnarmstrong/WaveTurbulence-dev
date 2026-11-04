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
public import WaveTurbulence.Frozen.Defs.GLeaf
public import WaveTurbulence.Frozen.Defs.GLeafToNode
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.Garden

/-!
# IsDecoration

Wave B tier B1 (WaveB1-Core.lean), source: T Def `defdec`. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

section Decorations

variable {w : ℕ} (G : Garden w)

/-- `κ : 𝒢 → V` is a **decoration** (T Def `defdec`): `κ_𝔫 = κ_{𝔫₁} - κ_{𝔫₂} + κ_{𝔫₃}` at every
branching node (children left, mid, right) and `κ_ℓ = κ_{ℓ'}` for paired leaves. Used with
`V = (Fin d → ℤ)` (lattice indices `n`, vectors `n/L`) and `V = Mom d`. -/
def IsDecoration {V : Type*} [AddCommGroup V] (κ : GNode G.tree → V) : Prop :=
  (∀ b : GBranch G.tree, κ b.toNode = κ (b.child 0) - κ (b.child 1) + κ (b.child 2)) ∧
    ∀ ℓ : GLeaf G.tree, κ ℓ.toNode = κ (G.pair ℓ).toNode

end Decorations
end WaveTurbulence
