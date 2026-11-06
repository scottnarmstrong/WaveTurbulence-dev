/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.MiniLeafRegion
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.PrefixStretch

/-! # No transported source endpoint falls into a newly inserted mini interval -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem stretch_below_inserted {w : ℕ} (a x : Address w) (p : Path)
    (hx : Below a (stretch a p x)) : Below (addrExt a p) (stretch a p x) := by
  by_cases ha : Below a x
  · obtain ⟨r,rfl⟩ := below_exists_frame a x ha
    rw [stretch_frame,← addrExt_append]
    exact below_extend _ _
  · rw [stretch_outside a p x ha] at hx
    exact (ha hx).elim

theorem frame_not_range_stretch {w : ℕ} (a : Address w) (p r : Path) (hr : ¬ p <+: r) :
    addrExt a r ∉ Set.range (stretch a p) := by
  rintro ⟨x,hx⟩
  have ha : Below a (stretch a p x) := by rw [hx]; exact below_extend _ _
  have hb := stretch_below_inserted a x p ha
  rw [hx] at hb
  exact hr ((below_frames_iff a p r).mp hb)

/-- Every new mini pair has a first endpoint outside the full relocation image. -/
theorem miniPairs_first_not_range {w : ℕ} (σ : Fin w → ℤˣ) (a : Address w) (m : MiniTreeCode)
    (q : Pair w) (hq : q ∈ miniPairs σ a m) : q.1 ∉ Set.range (stretch a [m.c,m.lone]) := by
  simp only [miniPairs,Finset.mem_insert,Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · unfold orient
    split_ifs
    · exact frame_not_range_stretch a _ _ (mini_side_not_below m).1
    · exact frame_not_range_stretch a _ _ (mini_side_not_below m).2.1
  · unfold orient
    split_ifs
    · exact frame_not_range_stretch a _ _ (mini_side_not_below m).2.2.1
    · exact frame_not_range_stretch a _ _ (mini_side_not_below m).2.2.2

end WaveTurbulence.Reg.Skeleton
