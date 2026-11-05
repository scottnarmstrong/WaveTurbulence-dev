/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.EraseTreeCouplePairBlocks
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.EraseTreeChainPairBlocks
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.FiniteBlockReplacement
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.RawChainInsertion
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedSigns

/-! # Exact complete matching factorization for erasing one tree replacement -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.eraseTree_raw_pairs {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (b : GBranch S.tree) :
    (D.raw hS).pairs = (((D.eraseTree b).raw hS).insertChain
      (inflatedPosition S (D.eraseTree b).tree b.toNode) (D.tree b)).pairs := by
  classical
  let E := D.eraseTree b
  let A := inflatedPosition S E.tree b.toNode
  let f (q : Pair w) := (stretch A (D.tree b).lonePath q.1,stretch A (D.tree b).lonePath q.2)
  let C (F : ReconstructionData S) (p : SourcePair S) :=
    ((F.couple p).pairsAt (inflatedPosition S F.tree (p.firstLeaf hS).toNode)
      (inflatedPosition S F.tree (p.secondLeaf hS).toNode)).toFinset
  let T (F : ReconstructionData S) (c : GBranch S.tree) :=
    ((F.tree c).pairsAt (nodeSign S.sig c.1) (inflatedPosition S F.tree c.toNode)).toFinset
  have hC : Finset.univ.biUnion (C D) = (Finset.univ.biUnion (C E)).image f := by
    rw [Finset.biUnion_image]
    apply Finset.biUnion_congr rfl
    intro p _
    exact D.eraseTree_couple_pair_block hS b p
  have hb : T E b = ∅ := by
    change (((D.eraseTree b).tree b).pairsAt _ _).toFinset = ∅
    rw [D.eraseTree_at]
    rfl
  have hT : Finset.univ.biUnion (T D) = (Finset.univ.biUnion (T E)).image f ∪ T D b :=
    biUnion_image_single (T D) (T E) f b hb (fun c hc => D.eraseTree_chain_pair_block b c hc)
  have hnew : ((D.tree b).pairsAt (nodeSign S.sig A) A).toFinset = T D b := by
    rw [inflatedPosition_sign S E.tree b.toNode]
    exact congrArg (fun a => ((D.tree b).pairsAt (nodeSign S.sig b.1) a).toFinset)
      (D.eraseTree_position_at b)
  change Finset.univ.biUnion (C D) ∪ Finset.univ.biUnion (T D) =
    (Finset.univ.biUnion (C E) ∪ Finset.univ.biUnion (T E)).image f ∪
      ((D.tree b).pairsAt (nodeSign S.sig A) A).toFinset
  rw [hC,hT,hnew,Finset.image_union]
  exact (Finset.union_assoc _ _ _).symm

end WaveTurbulence.Reg.Skeleton
