/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.BarePairInnerReplacement

/-! # Exact lower subtree of an outer mini context -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem miniTreeContext_subtreeAt_continuing (m : MiniTreeCode) (t : TTree) :
    (miniTreeContext m t).subtreeAt [m.c] = node3 (fun j => if j = m.lone then t else .leaf) := by
  obtain ⟨c,b⟩ := m
  fin_cases c <;> fin_cases b <;> simp [miniTreeContext,node3,TTree.subtreeAt]

end WaveTurbulence.Reg.Skeleton
