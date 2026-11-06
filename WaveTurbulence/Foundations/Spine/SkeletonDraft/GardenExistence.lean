/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.Termination
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CarrierRoundTrip

/-! # Actual garden carriers for terminal prime reductions

This supplies the existence half of DH21 Proposition 4.13 and DH21-2
Proposition 4.4. The source critical-pair and uniqueness proofs are separate.
-/

public section
namespace WaveTurbulence.Reg.Skeleton

/-- Every ordinary source garden is reconstructed from an actual prime garden.
No confluence premise is needed for this existence component. -/
theorem exists_prime_garden {w : ℕ} (G : Garden w) (hG : G.IsPlain) :
    ∃ S : Garden w, S.IsPlain ∧ Prime (rawOfGarden S) ∧
      Reconstructs (rawOfGarden S) (rawOfGarden G) := by
  obtain ⟨R,hR,hrec⟩ := exists_prime_predecessor (rawOfGarden G) (rawOfGarden_valid G hG)
  refine ⟨gardenOfRaw R hR.1,gardenOfRaw_plain _ _,?_,?_⟩
  · rw [rawOfGarden_gardenOfRaw]
    exact hR
  · rw [rawOfGarden_gardenOfRaw]
    exact hrec

end WaveTurbulence.Reg.Skeleton
