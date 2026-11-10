/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.SourceExpansionHistories
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.PrimeSkeletonUniqueness
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.SourcePrimeExistence

/-! # Source-form unique prime skeletons: arbitrary forward A/B construction histories

DH21 Proposition 4.13 / DH21-2 Proposition 4.4, prime existence and uniqueness
component. Regular/trivial equivalence, full replacement structure and counts
are separate obligations of C3.
-/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem prime_unique_of_source_reconstruction {w : ℕ} (G S T : Garden w) (hG : G.IsPlain)
    (hS : IsPrimeGarden S) (hT : IsPrimeGarden T)
    (hSG : Reconstructs (rawOfGarden S) (rawOfGarden G))
    (hTG : Reconstructs (rawOfGarden T) (rawOfGarden G)) : S = T :=
  prime_skeleton_unique G S T hS hT
    (gardenReduces_of_reconstructs S G hS.1 hG hSG)
    (gardenReduces_of_reconstructs T G hT.1 hG hTG)

/-- Every ordinary source garden is obtained from exactly one prime actual garden
by guarded source operations A and B. All literal trees and partner identities are unique. -/
theorem existsUnique_prime_reconstructs {w : ℕ} (G : Garden w) (hG : G.IsPlain) :
    ∃! S : Garden w, IsPrimeGarden S ∧ Reconstructs (rawOfGarden S) (rawOfGarden G) := by
  obtain ⟨S,hS,hSG⟩ := exists_source_prime_garden G hG
  refine ⟨S,⟨hS,hSG⟩,?_⟩
  intro T hT
  exact prime_unique_of_source_reconstruction G T S hG hT.1 hS hT.2 hSG

end WaveTurbulence.Reg.Skeleton
