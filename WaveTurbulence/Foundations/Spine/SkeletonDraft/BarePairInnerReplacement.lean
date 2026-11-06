/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.BarePairContext

/-! # Exact inner insertion and remaining attachment subtree of a bare pair -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem bare_pair_plug_inner (m : MiniTreeCode) (X : RegChain) (ζ : ℤˣ) (t : TTree) :
    Comb.replaceAt (miniTreeContext m t) [m.c]
      (X.plug (slotSign ζ m.c) (node3 (fun j => if j = m.lone then t else .leaf))) =
        (RegChain.pair m .triv .triv X .nil).plug ζ t := by
  rw [bare_pair_plug]
  obtain ⟨c,b⟩ := m
  fin_cases c <;> fin_cases b <;>
    simp [miniTreeContext,node3,MiniTreeCode.lone,Comb.replaceAt,RegChain.plug]

theorem bare_pair_subtree_rest (m : MiniTreeCode) (X : RegChain) (ζ : ℤˣ) (t : TTree) :
    Comb.subtree ((RegChain.pair m .triv .triv X .nil).plug ζ t)
      ([m.c] ++ X.lonePath ++ [m.lone]) = some t := by
  rw [bare_pair_plug]
  obtain ⟨c,b⟩ := m
  fin_cases c <;> fin_cases b <;>
    simp [node3,MiniTreeCode.lone,Comb.subtree,Comb.subtree_append,plug_subtree_lonePath,RegChain.plug]

end WaveTurbulence.Reg.Skeleton
