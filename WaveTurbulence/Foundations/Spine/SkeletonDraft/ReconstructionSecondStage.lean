/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ReconstructionDecorations
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.DecorationLookup
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ReconstructionPairListNodup

/-! # Regular couple replacement data on the actual bare-chain intermediate -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.barePart_pairs_eq_frames {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) :
    sourcePairs (D.barePart.garden hS) = ((D.decorations hS).map Prod.fst).toFinset :=
  (congrArg Raw.pairs (D.barePart.garden_raw hS)).trans
    ((D.barePart.pairList_toFinset hS).symm.trans (congrArg List.toFinset (D.decorations_frames hS).symm))

theorem ReconstructionData.decoration_frames_nodup {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) : ((D.decorations hS).map Prod.fst).Nodup :=
  (D.decorations_frames hS).symm ▸ D.barePart.pairList_nodup hS

noncomputable def ReconstructionData.secondStage {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) : ReconstructionData (D.barePart.garden hS) where
  tree := fun _ => .nil
  couple := fun p => (decorationAt (D.decorations hS) p.1 (List.mem_toFinset.mp
    ((D.barePart_pairs_eq_frames hS) ▸ p.2))).2
  tree_wf := fun _ => rfl
  couple_wf := fun p => D.decorations_wf hS _ (decorationAt_mem _ _ _)

theorem ReconstructionData.secondStage_frame {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (p : SourcePair (D.barePart.garden hS)) :
    let e := decorationAt (D.decorations hS) p.1 (List.mem_toFinset.mp
      ((D.barePart_pairs_eq_frames hS) ▸ p.2))
    e.1 = p.1 ∧ e.2 = (D.secondStage hS).couple p :=
  ⟨decorationAt_frame _ _ _,rfl⟩

end WaveTurbulence.Reg.Skeleton
