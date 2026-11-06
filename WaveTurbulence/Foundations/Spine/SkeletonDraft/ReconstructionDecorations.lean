/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ChainDecorationBlocks
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ReconstructionBarePart
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.FiniteBlockLists

/-! # All regular couple decorations on the literal bare-chain intermediate -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

/-- Original source couple slots followed by the legal source-ordered side couples of every tree slot. -/
noncomputable def ReconstructionData.decorations {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) : List (Decoration w) :=
  Finset.univ.toList.map (fun p : SourcePair S =>
    ((inflatedPosition S D.tree (p.firstLeaf hS).toNode,
      inflatedPosition S D.tree (p.secondLeaf hS).toNode),D.couple p)) ++
  Finset.univ.toList.flatMap (fun b : GBranch S.tree =>
    chainDecorationBlocks (D.tree b) (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode))

theorem ReconstructionData.decorations_frames {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) :
    (D.decorations hS).map Prod.fst = D.barePart.pairList hS := by
  simp only [ReconstructionData.decorations,List.map_append,List.map_map,List.map_flatMap,
    chainDecorationBlocks_frames,ReconstructionData.pairList]
  have hpos (a : GNode S.tree) : inflatedPosition S (fun b => eraseChainCouples (D.tree b)) a =
      inflatedPosition S D.tree a := D.barePart_position a
  simp only [ReconstructionData.barePart,RegCpl.pairsAt,hpos,← List.map_eq_flatMap,Function.comp_def]

theorem ReconstructionData.decorations_pairs {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) :
    (D.decorations hS).flatMap (fun e => e.2.pairsAt e.1.1 e.1.2) = D.pairList hS := by
  simp only [ReconstructionData.decorations,List.flatMap_append,List.flatMap_map,List.flatMap_assoc,
    chainDecorationBlocks_pairs,ReconstructionData.pairList]

theorem ReconstructionData.decorations_wf {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (e : Decoration w) (he : e ∈ D.decorations hS) :
    e.2.wf = true := by
  rcases List.mem_append.mp he with he | he
  · obtain ⟨p,_,rfl⟩ := List.mem_map.mp he
    exact D.couple_wf p
  · obtain ⟨b,_,he⟩ := List.mem_flatMap.mp he
    exact chainDecorationBlocks_wf (D.tree b) (D.tree_wf b) _ _ e he

end WaveTurbulence.Reg.Skeleton
