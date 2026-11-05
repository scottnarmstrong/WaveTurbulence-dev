/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.PinnedRelocation
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BContext.InsertionCovariance

/-! # Pair transport for a couple block with its actual moved attachment roots -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem pinned_couple_frames_of_mem {w : ℕ} (Q : RegCpl) (a b target : Address w)
    (m : MiniTreeCode) (hab : IncompAddr a b) (ht : target ∈ coupleNodes Q a b) :
    pinnedRelocate target m a = a ∧ pinnedRelocate target m b = b := by
  rcases coupleNodes_below Q a b target ht with ha | hb
  · exact ⟨pinnedRelocate_of_below _ _ _ ha,
      pinnedRelocate_of_not_below _ _ _ (fun h => hab.1 (below_trans ha h))⟩
  · exact ⟨pinnedRelocate_of_not_below _ _ _ (fun h => hab.2 (below_trans hb h)),
      pinnedRelocate_of_below _ _ _ hb⟩

/-- Conditional local helper; actual-node extraction supplies the location alternative. -/
theorem normalizedCouple_pairs_pinned {w : ℕ} (Q : RegCpl) (σ : Fin w → ℤˣ)
    (a b target : Address w) (m : MiniTreeCode) (hab : IncompAddr a b)
    (ha : nodeSign σ a = 1) (hb : nodeSign σ b = -1)
    (hl : target ∈ coupleNodes Q a b ∨ (¬ Below a target ∧ ¬ Below b target)) :
    ((normalizeCouple (insertMiniCouple Q a b target m)).pairsAt
      (pinnedRelocate target m a) (pinnedRelocate target m b)).toFinset =
      (Q.pairsAt a b).toFinset.image (fun p =>
        (relocate target m.c m.lone p.1,relocate target m.c m.lone p.2)) ∪
      if target ∈ coupleNodes Q a b then miniPairs σ target m else ∅ := by
  classical
  by_cases ht : target ∈ coupleNodes Q a b
  · obtain ⟨hA,hB⟩ := pinned_couple_frames_of_mem Q a b target m hab ht
    rw [hA,hB,ite_eq_left ht]
    exact BContext.normalizedCouple_pairs Q σ a b target m hab ha hb ht
  · have hn := hl.resolve_left ht
    rw [ite_eq_right ht,Finset.union_empty,insertMiniCouple_outside Q a b target m ht,
      pinnedRelocate_eq_relocate target a m hn.1,pinnedRelocate_eq_relocate target b m hn.2]
    have he : ((normalizeCouple Q).pairsAt (relocate target m.c m.lone a)
        (relocate target m.c m.lone b)).toFinset =
        (Q.pairsAt (relocate target m.c m.lone a) (relocate target m.c m.lone b)).toFinset := by
      ext z
      simp only [List.mem_toFinset,mem_normalizeCouple_pairsAt]
    rw [he,couple_pairsAt_map_local Q (relocate target m.c m.lone) a b
      (BContext.relocate_respectsAt_of_not_below target a m.c m.lone hn.1)
      (BContext.relocate_respectsAt_of_not_below target b m.c m.lone hn.2),list_map_toFinset]

end WaveTurbulence.Reg.Skeleton
