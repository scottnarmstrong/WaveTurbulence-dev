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
# IsLayering

Wave B tier B1 (WaveB1-Core.lean), source: T Def `deflayer`. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

/-- A **layering** `𝔏 : 𝒢 → ℕ` (T Def `deflayer`): `𝔏_{𝔫'} ≤ 𝔏_𝔫` whenever `𝔫'` is a child of
`𝔫`, and `𝔏_ℓ = 𝔏_{ℓ'}` for paired leaves. (`0 ≤ 𝔏` is built into `ℕ`; DESIGN Q1.) -/
def IsLayering {w : ℕ} (G : Garden w) (𝔏 : GNode G.tree → ℕ) : Prop :=
  (∀ b : GBranch G.tree, ∀ i : Fin 3, 𝔏 (b.child i) ≤ 𝔏 b.toNode) ∧
    ∀ ℓ : GLeaf G.tree, 𝔏 ℓ.toNode = 𝔏 (G.pair ℓ).toNode

end WaveTurbulence
