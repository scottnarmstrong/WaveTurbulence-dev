/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.RegRedDraft.RootedLayering
public import WaveTurbulence.Foundations.Molecule.RegRedDraft.NativeCoupleBranches
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionRegularCouples
public import WaveTurbulence.Foundations.RegStruct.CarrierUniqueness

/-! # The actual layered regular couples occurring in the skeleton reduction -/

@[expose] public section
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

noncomputable def layeredReconstruction {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) : LayeredGarden w := ⟨D.garden hS,layer,hLayer⟩

theorem nativeCoupleForest_eq {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (p : SourcePair S) :
    nativeCoupleForest D hS p = Comb.twoRootSubforest
      (D.decodedNode hS (D.garden_decodes hS) (p.firstLeaf hS).toNode)
      (D.decodedNode hS (D.garden_decodes hS) (p.secondLeaf hS).toNode)
      (Comb.subCouple_incomparable (D.decoded_couple_isSubCouple hS (D.garden_decodes hS) p)) := by
  apply rootedSubforest_ext
  intro j
  fin_cases j <;> exact Subtype.ext rfl

theorem nativeCoupleForest_closed {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (p : SourcePair S) :
    (D.garden hS).CompletelyPaired (Comb.RootedSubforest.leafSet (nativeCoupleForest D hS p)) := by
  rw [nativeCoupleForest_eq]
  exact Comb.subCouple_forest_closed (D.decoded_couple_isSubCouple hS (D.garden_decodes hS) p)

theorem nativeCoupleGarden_eq {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (p : SourcePair S) :
    Comb.RootedSubforest.inducedGarden (G := D.garden hS) (nativeCoupleForest D hS p)
      (nativeCoupleForest_closed D hS p) =
      decodedCouple (D.couple p) := by
  have he : Comb.RootedSubforest.inducedGarden (G := D.garden hS) (nativeCoupleForest D hS p)
      (nativeCoupleForest_closed D hS p) =
      Comb.subCoupleGarden (D.decoded_couple_isSubCouple hS (D.garden_decodes hS) p) :=
    inducedGarden_congr (G := D.garden hS) (nativeCoupleForest D hS p) _
    (nativeCoupleForest_eq D hS p) (nativeCoupleForest_closed D hS p)
    (Comb.subCouple_forest_closed (D.decoded_couple_isSubCouple hS (D.garden_decodes hS) p))
  exact he.trans (decodedCouple_unique _ _ (D.decoded_couple_decodes hS (D.garden_decodes hS) p))

noncomputable def nativeCoupleLayered {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (p : SourcePair S) : LayeredGarden 2 :=
  rootedLayeredGarden (layeredReconstruction D hS layer hLayer) (nativeCoupleForest D hS p)
    (nativeCoupleForest_closed D hS p)

theorem nativeCoupleLayered_garden {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (p : SourcePair S) :
    (nativeCoupleLayered D hS layer hLayer p).garden = decodedCouple (D.couple p) :=
  nativeCoupleGarden_eq D hS p

end WaveTurbulence.RegRed
