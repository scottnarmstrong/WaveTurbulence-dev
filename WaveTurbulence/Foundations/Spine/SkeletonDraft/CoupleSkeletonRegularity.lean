/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.TrivialCoupleRegular
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.RegularCoupleReduction
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.SourcePrimeUniqueness

/-! # The source couple skeleton is trivial exactly for regular couples (DH21 Proposition 4.13) -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem couple_regular_iff_prime_skeleton_trivial (G S : Garden 2) (hG : IsCouple G)
    (hS : IsPrimeGarden S) (hSG : Reconstructs (rawOfGarden S) (rawOfGarden G)) :
    IsRegularCouple G ↔ IsTrivialGarden S := by
  have hs := gardenReduces_of_reconstructs S G hS.1 hG.1 hSG
  constructor
  · intro hr
    have ht : IsTrivialGarden (decodedCouple .triv) :=
      ⟨(decodedCouple_decodes .triv).1.1,by intro j; fin_cases j <;> rfl⟩
    have he := prime_skeleton_unique G S (decodedCouple .triv) hS ht.isPrimeGarden hs
      (regularCouple_reduces_trivial hr)
    exact he.symm ▸ ht
  · intro ht
    have hc : IsCouple S := ⟨hS.1,hs.sig_eq.trans hG.2⟩
    exact regularCouple_closed_reconstructs S G (trivial_couple_regular S hc ht) hG.1 hSG

end WaveTurbulence.Reg.Skeleton
