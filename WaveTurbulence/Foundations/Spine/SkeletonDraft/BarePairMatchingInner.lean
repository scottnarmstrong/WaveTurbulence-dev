/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.StretchChildSiblings

/-! # Exact side-pair transport through the inner bare chain insertion -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem bare_pair_pairsAt_inner {w : ℕ} (m : MiniTreeCode) (X : RegChain)
    (σ : Fin w → ℤˣ) (a : Address w) :
    ((RegChain.pair m .triv .triv X .nil).pairsAt (nodeSign σ a) a).toFinset =
      (miniPairs σ a m).image (fun p =>
        (stretch (addrExt a [m.c]) X.lonePath p.1,stretch (addrExt a [m.c]) X.lonePath p.2)) ∪
      (X.pairsAt (slotSign (nodeSign σ a) m.c) (addrExt a [m.c])).toFinset := by
  classical
  have hr : m.red.1 ≠ m.c := by
    obtain ⟨c,b⟩ := m
    fin_cases c <;> fin_cases b <;> decide
  have hg : m.green.1 ≠ m.c := by
    obtain ⟨c,b⟩ := m
    fin_cases c <;> fin_cases b <;> decide
  by_cases hred : slotSign (nodeSign σ a) m.red.1 = 1 <;>
    by_cases hgreen : slotSign (nodeSign σ a) m.green.1 = 1 <;>
    simp [RegChain.pairsAt,RegCpl.pairsAt,RegChain.lonePath,miniPairs,orient,hred,hgreen,
      stretch_child_sibling a m.c m.red.1 X.lonePath hr,
      stretch_child_sibling a m.c m.green.1 X.lonePath hg,stretch_child_descendant,
      Finset.union_assoc]

end WaveTurbulence.Reg.Skeleton
