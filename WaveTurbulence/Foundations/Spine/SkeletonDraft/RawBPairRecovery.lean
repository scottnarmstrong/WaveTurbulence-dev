/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.StretchGap

/-! # Raw B insertion retains exactly the old matching outside its two new mini pairs -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem Raw.opB_pairs_erase_mini {w : ℕ} (R : Raw w) (a : Address w) (m : MiniTreeCode) :
    (R.opB a m).pairs \ miniPairs R.sig a m =
      R.pairs.image (fun p => (relocate a m.c m.lone p.1,relocate a m.c m.lone p.2)) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hp,hn⟩ := Finset.mem_sdiff.mp hp
    change p ∈ _ ∪ miniPairs R.sig a m at hp
    exact (Finset.mem_union.mp hp).resolve_right hn
  · intro hp
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hp,?_⟩
    intro hm
    obtain ⟨q,hq,he⟩ := Finset.mem_image.mp hp
    apply miniPairs_first_not_range R.sig a m p hm
    refine ⟨q.1,?_⟩
    have hx := congrArg (fun z : Pair w => z.1) he
    simpa only [relocate_eq_stretch] using hx

theorem relocate_pairs_injective {w : ℕ} (a : Address w) (m : MiniTreeCode) :
    Function.Injective (fun p : Pair w => (relocate a m.c m.lone p.1,relocate a m.c m.lone p.2)) := by
  intro p q he
  apply Prod.ext
  · exact stretch_injective a [m.c,m.lone] (congrArg (fun z : Pair w => z.1) he)
  · exact stretch_injective a [m.c,m.lone] (congrArg (fun z : Pair w => z.2) he)

/-- Equality after the same B insertion forces equality of the entire original finite matching. -/
theorem Raw.opB_pairs_injective {w : ℕ} (R T : Raw w) (a : Address w) (m : MiniTreeCode)
    (he : R.opB a m = T.opB a m) : R.pairs = T.pairs := by
  have hp := congrArg (fun U : Raw w => U.pairs \ miniPairs U.sig a m) he
  have hi : R.pairs.image (fun p => (relocate a m.c m.lone p.1,relocate a m.c m.lone p.2)) =
      T.pairs.image (fun p => (relocate a m.c m.lone p.1,relocate a m.c m.lone p.2)) :=
    (R.opB_pairs_erase_mini a m).symm.trans (hp.trans (T.opB_pairs_erase_mini a m))
  exact Finset.image_injective (relocate_pairs_injective a m) hi

end WaveTurbulence.Reg.Skeleton
