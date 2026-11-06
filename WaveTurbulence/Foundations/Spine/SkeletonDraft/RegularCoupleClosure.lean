/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.RegularCoupleHistories
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.GardenRawHistories

/-! # The pinned source regular-couple predicate is closed under the exact guarded construction relation -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem matchesCouple_of_rawCplSet_eq (G : Garden 2) (R : RawCpl) (hG : G.IsPlain)
    (he : rawOfGarden G = rawCplSet R) : G.MatchesCouple R.1 R.2 := by
  have hs := congrArg Raw.sig he
  change G.sig = ![1,-1] at hs
  have ht := congrArg Raw.tree he
  change G.tree = R.tree at ht
  have hp := congrArg Raw.pairs he
  change sourcePairs G = R.2.toFinset at hp
  refine ⟨⟨hG,hs⟩,?_,?_,?_⟩
  · simpa [RawCpl.tree] using congrFun ht (0 : Fin 2)
  · simpa [RawCpl.tree] using congrFun ht (1 : Fin 2)
  · intro ℓ
    rcases sourcePairs_partner G hG ℓ with hm | hm
    · apply (mem_symmPairs_iff _ _).mpr
      left
      exact List.mem_toFinset.mp (hp ▸ hm)
    · apply (mem_symmPairs_iff _ _).mpr
      right
      exact List.mem_toFinset.mp (hp ▸ hm)

theorem reconstructs_regular_history {R : RawCpl} (hR : RawRegular R) {T : Raw 2}
    (h : Reconstructs (rawCplSet R) T) : ∃ Q : RawCpl, RawRegular Q ∧ rawCplSet Q = T := by
  induction h with
  | refl => exact ⟨R,hR,rfl⟩
  | @tail U V hr hs ih =>
    obtain ⟨Q,hQ,he⟩ := ih
    cases hs with
    | opA x y k hU hp =>
      have hm : (x,y) ∈ Q.2 := by
        apply List.mem_toFinset.mp
        change (x,y) ∈ (rawCplSet Q).pairs
        rw [he]
        exact hp
      refine ⟨Q.opA x y k,RawRegular.opA k hQ hm,?_⟩
      exact (rawCplSet_opA Q (RawRegular.pairs_nodup hQ) x y k).trans
        (congrArg (fun A : Raw 2 => A.opA x y k) he)
    | opB a m hU ha =>
      have ht := congrArg Raw.tree he
      change Q.tree = U.tree at ht
      have hn : a.2 ∈ (Q.tree a.1).nodes := by rw [ht]; exact ha
      refine ⟨Q.opB a m,RawRegular.opB m hQ hn,?_⟩
      exact (rawCplSet_opB Q a m).trans (congrArg (fun A : Raw 2 => A.opB a m) he)

theorem regularCouple_closed_reconstructs (S G : Garden 2) (hS : IsRegularCouple S) (hG : G.IsPlain)
    (h : Reconstructs (rawOfGarden S) (rawOfGarden G)) : IsRegularCouple G := by
  obtain ⟨R,hR,hm⟩ := hS
  have hs := rawOfGarden_eq_regular_history S R hR hm
  rw [hs] at h
  obtain ⟨Q,hQ,hQG⟩ := reconstructs_regular_history hR h
  exact ⟨Q,hQ,matchesCouple_of_rawCplSet_eq G Q hG hQG.symm⟩

end WaveTurbulence.Reg.Skeleton
