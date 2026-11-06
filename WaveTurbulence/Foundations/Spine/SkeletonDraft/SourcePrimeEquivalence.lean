/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ForwardAMini
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ForwardBMini
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.SourcePrimeExistence

/-! # The forward and inverse source definitions of prime agree exactly -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem Expand.sourceMini {w : ℕ} {R T : Raw w} (h : Expand R T) (G : Garden w)
    (he : rawOfGarden G = T) : Nonempty (MiniOccurrence G) := by
  cases h with
  | opA x y k hR hp =>
    obtain ⟨b,c,_,_,hm⟩ := sourceMiniA_of_raw_opA R hR G x y k hp he
    exact ⟨.opA b c k hm⟩
  | opB a k hR ha =>
    obtain ⟨b,c,_,_,hm⟩ := sourceMiniB_of_raw_opB R G a k ha he
    exact ⟨.opB b c k hm⟩

/-- DH21/DH21-2's absence of a forward predecessor and TARGET's absence of an
embedded mini piece are equivalent on the complete ordinary source carrier. -/
theorem isPrimeGarden_iff_raw_prime {w : ℕ} (G : Garden w) (hG : G.IsPlain) :
    IsPrimeGarden G ↔ Prime (rawOfGarden G) := by
  constructor
  · intro hp
    refine ⟨rawOfGarden_valid G hG,?_⟩
    intro R hR
    exact hp.2 (hR.sourceMini G rfl)
  · exact isPrimeGarden_of_raw_prime G hG

end WaveTurbulence.Reg.Skeleton
