/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ReconstructionSecondStage
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.CoupleOnlyPairFormula

/-! # Exact complete matching of the bare-chain then regular-couple decomposition -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.secondStage_pairs {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) :
    ((D.secondStage hS).raw (D.barePart.garden_plain hS)).pairs = (D.raw hS).pairs := by
  classical
  let H := D.barePart.garden hS
  let E := D.secondStage hS
  let L := D.decorations hS
  have he : E.attachmentPairs (D.barePart.garden_plain hS) =
      Finset.univ.biUnion (fun p : SourcePair H => ((E.couple p).pairsAt p.1.1 p.1.2).toFinset) :=
    E.attachmentPairs_of_nil_tree _ (fun _ => rfl)
  have hd : (D.raw hS).pairs = (L.flatMap (fun e => e.2.pairsAt e.1.1 e.1.2)).toFinset :=
    (D.pairList_toFinset hS).symm.trans (congrArg List.toFinset (D.decorations_pairs hS).symm)
  change E.attachmentPairs (D.barePart.garden_plain hS) = _
  rw [he,hd]
  ext q
  constructor
  · intro hq
    obtain ⟨p,_,hq⟩ := Finset.mem_biUnion.mp hq
    let e := decorationAt L p.1 (List.mem_toFinset.mp ((D.barePart_pairs_eq_frames hS) ▸ p.2))
    have hem : e ∈ L := decorationAt_mem _ _ _
    have hef : e.1 = p.1 := decorationAt_frame _ _ _
    have hec : e.2 = E.couple p := rfl
    apply List.mem_toFinset.mpr
    apply List.mem_flatMap.mpr
    refine ⟨e,hem,?_⟩
    have hh : q ∈ e.2.pairsAt e.1.1 e.1.2 := by
      rw [hef,hec]
      exact List.mem_toFinset.mp hq
    exact hh
  · intro hq
    obtain ⟨e,he,hq⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hq)
    have hf : e.1 ∈ sourcePairs H := (D.barePart_pairs_eq_frames hS).symm ▸
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨e,he,rfl⟩)
    let p : SourcePair H := ⟨e.1,hf⟩
    have hlookup : decorationAt L p.1 (List.mem_toFinset.mp ((D.barePart_pairs_eq_frames hS) ▸ p.2)) = e :=
      decorationAt_eq L (D.decoration_frames_nodup hS) p.1 _ e he rfl
    have hc : E.couple p = e.2 := congrArg Prod.snd hlookup
    apply Finset.mem_biUnion.mpr
    refine ⟨p,Finset.mem_univ _,?_⟩
    rw [hc]
    exact List.mem_toFinset.mpr hq

end WaveTurbulence.Reg.Skeleton
