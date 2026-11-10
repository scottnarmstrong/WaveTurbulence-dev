/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionPairListSupport
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionPairListSigns
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionLeafCoverage
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionEndpointCount
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.GardenOfPairsCanonical
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CarrierRoundTrip

/-! # Constructing an ordinary actual garden from every literal replacement assignment -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

/-- The complete ordinary matching specified by the literal replacement forest and pair blocks. -/
noncomputable def ReconstructionData.garden {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) : Garden w :=
  gardenOfPairs (D.forest hS) S.sig (D.pairList hS) (D.pairList_endpoints_valid hS)
    (D.forest_pairList_cover hS) (D.pairList_endpoint_count hS) (D.pairList_signs hS)

theorem ReconstructionData.garden_plain {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) : (D.garden hS).IsPlain :=
  gardenOfPairs_plain _ _ _ _ _ _ _

theorem ReconstructionData.garden_raw {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) : rawOfGarden (D.garden hS) = D.raw hS := by
  apply Raw.ext
  · rfl
  · rfl
  · exact (sourcePairs_gardenOfPairs _ _ _ _ _ _ _).trans (D.pairList_toFinset hS)

theorem ReconstructionData.garden_decodes {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) : D.Decodes hS (D.garden hS) :=
  ⟨D.garden_plain hS,(D.garden_raw hS).symm⟩

theorem ReconstructionData.raw_valid {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) : (D.raw hS).Valid :=
  D.garden_raw hS ▸ rawOfGarden_valid (D.garden hS) (D.garden_plain hS)

theorem ReconstructionData.existsUnique_decodes {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) : ∃! G : Garden w, D.Decodes hS G := by
  refine ⟨D.garden hS,D.garden_decodes hS,?_⟩
  intro G hG
  exact rawOfGarden_injective_plain hG.1 (D.garden_plain hS)
    (hG.2.symm.trans (D.garden_raw hS).symm)

end WaveTurbulence.Reg.Skeleton
