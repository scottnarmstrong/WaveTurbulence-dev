/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.SubforestOpenGraph

/-! # Actual boundary input slots in the full subforest open port injection -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem subforestOpenPort_root_zero {w v : ℕ} (G : Garden w) (E : Comb.RootedSubforest G.tree v)
    (hc : G.CompletelyPaired (Comb.RootedSubforest.leafSet E)) (j : Fin v) :
    subforestOpenPort G E hc (.inl j,0) = (ambientWithPadding (v := v) G).incoming (E.root j) := by
  change (ambientWithPadding (v := v) G).portEmbedding (subforestPortEmbedding G E hc (.inl j)) = _
  rw [subforestPort_root]
  rfl

end WaveTurbulence.Reg.Skeleton
