/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GBranch
public import WaveTurbulence.Frozen.Defs.GBranchToNode
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenOrder
public import WaveTurbulence.Frozen.Defs.IsCanonC
public import WaveTurbulence.Frozen.Defs.KernelKgen
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenAttachNodes
public import WaveTurbulence.Frozen.Defs.LayeredGardenAttachedOrder
public import WaveTurbulence.Frozen.Defs.LayeredGardenTreeKindOK
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.TTreeBranching
public import WaveTurbulence.Frozen.Defs.TTreePath
public import WaveTurbulence.Frozen.Defs.TreeKind
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsN

/-!
# coupleSum

Wave B tier B1 (WaveB1-Flower.lean), source: T L2312. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open Classical in
/-- **The restricted couple sum** (T L2312). It sums over the couples `𝒬 ∈ 𝒞_{p+1}` of order `N`
with attached gardens of order `≤ N_p` and trees of kind `kind`. With `dt`, the roots are layer-`p`
branching nodes and have time `t` (`δ(t_𝔯 − t)` of `∂_t`). The root vector is `k ∈ ℝ^d`, as in `KQ`.
Without `dt` and with kind `tr` this is `truncSumC` (bridge in the probes).

The roots must be in layer `p` (F78). The term `δ(t_𝔯 − t)` comes from `∂_t` of the tree expansion, whose roots
are top-layer branching nodes; `∂_t 𝒥_• = 0`. So a couple whose top tree is trivial, with a lower-layer garden
attached at its root, is excluded. -/
noncomputable def coupleSum (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) (kind : TreeKind)
    (dt : Bool) (t : ℝ) (k : Mom P.d) : ℂ :=
  ∑ᶠ (LG : LayeredGarden 2) (_ : IsCanonC (p + 1) LG ∧
      (∀ u ∈ LG.attachNodes p, LG.attachedOrder p u ≤ P.N p) ∧ LG.garden.order = N ∧
      LG.TreeKindOK p (P.N (p + 1)) kind ∧
      (dt = true → ∀ j : Fin 2, ∃ b : GBranch LG.garden.tree, b.1 = (j, []) ∧ LG.layer b.toNode = p)),
    kernelKgen P.L P.γ P.δ F LG (fun b => if dt = true ∧ b.1.2 = [] then some t else none) ∅
      (fun _ => 1) (fun _ => t) k (fun _ => 0) 0

end WaveTurbulence
