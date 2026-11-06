/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.BarePairContext

/-! # Exact final rest insertion in the outer-mini factorization of a bare pair -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem bare_pair_plug_rest (m : MiniTreeCode) (X Y : RegChain) (ζ : ℤˣ) (t : TTree) :
    Comb.replaceAt ((RegChain.pair m .triv .triv X .nil).plug ζ t)
      ([m.c] ++ X.lonePath ++ [m.lone]) (Y.plug ζ t) =
        (RegChain.pair m .triv .triv X Y).plug ζ t := by
  rw [bare_pair_plug,bare_pair_plug]
  obtain ⟨c,b⟩ := m
  fin_cases c <;> fin_cases b <;>
    simp [node3,MiniTreeCode.lone,Comb.replaceAt,replaceAt_plug_lone_append,
      RegChain.plug,slotSign]

end WaveTurbulence.Reg.Skeleton
