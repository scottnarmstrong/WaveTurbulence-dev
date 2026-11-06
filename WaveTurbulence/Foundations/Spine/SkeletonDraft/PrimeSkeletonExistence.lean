/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.PrimeSkeletonUniqueness

/-! # Unique actual prime skeletons under literal source A/B reduction -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem exists_prime_skeleton {w : ℕ} (G : Garden w) (hG : G.IsPlain) :
    ∃ S : Garden w, IsPrimeGarden S ∧ GardenReduces G S := by
  classical
  have aux : ∀ n, ∀ G : Garden w, G.order = n → G.IsPlain →
      ∃ S : Garden w, IsPrimeGarden S ∧ GardenReduces G S := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro G he hG
      by_cases hm : Nonempty (MiniOccurrence G)
      · obtain ⟨M⟩ := hm
        cases M with
        | opA b c k hm =>
          let H := collapseCoupleGarden (hm.isSubCouple hG)
          have hs : GardenStep G H := GardenStep.opA G hG b c k hm
          have ho := hs.order
          obtain ⟨S,hS,hr⟩ := ih H.order (by omega) H rfl hs.target_plain
          exact ⟨S,hS,hr.head hs⟩
        | opB b c k hm =>
          let H := collapsePairedTreeGarden (hm.isSubPairedTree hG)
          have hs : GardenStep G H := GardenStep.opB G hG b c k hm
          have ho := hs.order
          obtain ⟨S,hS,hr⟩ := ih H.order (by omega) H rfl hs.target_plain
          exact ⟨S,hS,hr.head hs⟩
      · exact ⟨G,⟨hG,hm⟩,Relation.ReflTransGen.refl⟩
  exact aux G.order G rfl hG

/-- DH21 Proposition 4.13 / DH21-2 Proposition 4.4: the source prime skeleton exists uniquely. -/
theorem existsUnique_prime_skeleton {w : ℕ} (G : Garden w) (hG : G.IsPlain) :
    ∃! S : Garden w, IsPrimeGarden S ∧ GardenReduces G S := by
  obtain ⟨S,hS,hr⟩ := exists_prime_skeleton G hG
  refine ⟨S,⟨hS,hr⟩,?_⟩
  intro H hH
  exact prime_skeleton_unique G H S hH.1 hS hH.2 hr

end WaveTurbulence.Reg.Skeleton
