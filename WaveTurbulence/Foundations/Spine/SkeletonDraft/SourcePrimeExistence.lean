/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniARecovery
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniBRecovery
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.PrimeGraph
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.GardenExistence

/-! # Existence of prime skeletons with the literal source prime predicate -/

public section
namespace WaveTurbulence.Reg.Skeleton

/-- A raw terminal ordinary garden contains neither kind of actual embedded source mini. -/
theorem isPrimeGarden_of_raw_prime {w : ℕ} (G : Garden w) (hG : G.IsPlain)
    (hp : Prime (rawOfGarden G)) : IsPrimeGarden G := by
  refine ⟨hG,?_⟩
  rintro ⟨M⟩
  cases M with
  | opA b c k h =>
    rcases Int.units_eq_one_or (nodeSign G.sig b.1) with hb | hb
    · exact hp.2 _ (h.predecessor hG hb)
    · have hc : nodeSign G.sig c.1 = 1 := by
        have hs : nodeSign G.sig c.1 = -nodeSign G.sig b.1 := h.1
        rw [hb] at hs
        simpa only [neg_neg] using hs
      exact hp.2 _ (h.flip.predecessor hG hc)
  | opB b c m h => exact hp.2 _ (h.predecessor hG)

/-- Every ordinary source garden is reconstructed by actual A/B moves from a garden
with no embedded mini couple and no embedded mini tree. -/
theorem exists_source_prime_garden {w : ℕ} (G : Garden w) (hG : G.IsPlain) :
    ∃ S : Garden w, IsPrimeGarden S ∧ Reconstructs (rawOfGarden S) (rawOfGarden G) := by
  obtain ⟨S,hS,hp,hr⟩ := exists_prime_garden G hG
  exact ⟨S,isPrimeGarden_of_raw_prime S hS hp,hr⟩

end WaveTurbulence.Reg.Skeleton
