/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ReconstructionExistence
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.GeneralReconstructionUniqueness
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.GardenRawHistories
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.SourcePrimeUniqueness

/-! # DH21 4.13 and DH21-2 4.4: unique prime skeleton and unique literal replacements -/

public section
namespace WaveTurbulence.Reg.Skeleton

/-- Literal regular replacement data and the source A/B reconstruction history agree. -/
theorem reconstructs_iff_exists_reconstructionData {w : ℕ} (S G : Garden w)
    (hS : S.IsPlain) (hG : G.IsPlain) :
    Reconstructs (rawOfGarden S) (rawOfGarden G) ↔
      ∃ D : ReconstructionData S, D.Decodes hS G := by
  constructor
  · exact exists_reconstructionData_of_reconstructs S G hS hG
  · rintro ⟨D,hd⟩
    obtain ⟨trace,ht⟩ := D.reduction_trace hS G hd
    exact trace.reduces.raw_reconstructs

/-- DH21 4.13, including the general-couple uniqueness obligation at L833:
all regular replacements over the actual prime skeleton exist and are unique. -/
theorem existsUnique_reconstructionData {w : ℕ} (S G : Garden w)
    (hS : IsPrimeGarden S) (hG : G.IsPlain)
    (h : Reconstructs (rawOfGarden S) (rawOfGarden G)) :
    ∃! D : ReconstructionData S, D.Decodes hS.1 G := by
  obtain ⟨D,hd⟩ := exists_reconstructionData_of_reconstructs S G hS.1 hG h
  exact ⟨D,hd,fun E he => reconstructionData_unique E D hS he hd⟩

/-- DH21 4.13 / DH21-2 4.4: every ordinary garden has a unique actual prime
skeleton, and all of its literal regular replacements are uniquely determined. -/
theorem existsUnique_prime_with_replacements {w : ℕ} (G : Garden w) (hG : G.IsPlain) :
    ∃! S : Garden w, ∃ hS : IsPrimeGarden S,
      ∃! D : ReconstructionData S, D.Decodes hS.1 G := by
  obtain ⟨S,⟨hS,hSG⟩,hu⟩ := existsUnique_prime_reconstructs G hG
  refine ⟨S,⟨hS,existsUnique_reconstructionData S G hS hG hSG⟩,?_⟩
  rintro T ⟨hT,D,hd,hunique⟩
  exact hu T ⟨hT,(reconstructs_iff_exists_reconstructionData T G hT.1 hG).mpr ⟨D,hd⟩⟩

end WaveTurbulence.Reg.Skeleton
