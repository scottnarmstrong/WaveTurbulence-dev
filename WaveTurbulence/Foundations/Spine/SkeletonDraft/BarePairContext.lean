/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ChainHoleReplacement

/-! # Literal outer-mini factorization of a bare chain pair constructor -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem bare_pair_plug (m : MiniTreeCode) (X Y : RegChain) (ζ : ℤˣ) (t : TTree) :
    (RegChain.pair m .triv .triv X Y).plug ζ t =
      node3 (fun i => if i = m.c then X.plug (slotSign ζ m.c)
        (node3 (fun j => if j = m.lone then Y.plug ζ t else .leaf)) else .leaf) := by
  obtain ⟨c,b⟩ := m
  fin_cases c <;> fin_cases b <;>
    simp [RegChain.plug,RegCpl.trees,treeOfSign,node3,MiniTreeCode.lone,slotSign]

end WaveTurbulence.Reg.Skeleton
