/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionCoupleUpdate

/-! # The literal matching blocks outside one source couple replacement slot -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

noncomputable def ReconstructionData.couplePairBlock {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (p : SourcePair S) : Finset (Pair w) :=
  ((D.couple p).pairsAt (inflatedPosition S D.tree (p.firstLeaf hS).toNode)
    (inflatedPosition S D.tree (p.secondLeaf hS).toNode)).toFinset

noncomputable def ReconstructionData.coupleBackground {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (p : SourcePair S) : Finset (Pair w) :=
  (Finset.univ.erase p).biUnion (D.couplePairBlock hS) ∪
    Finset.univ.biUnion (fun b : GBranch S.tree =>
      ((D.tree b).pairsAt (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode)).toFinset)

theorem ReconstructionData.attachmentPairs_eq_background_union {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (p : SourcePair S) :
    D.attachmentPairs hS = D.coupleBackground hS p ∪ D.couplePairBlock hS p := by
  classical
  have hc : Finset.univ.biUnion (D.couplePairBlock hS) =
      D.couplePairBlock hS p ∪ (Finset.univ.erase p).biUnion (D.couplePairBlock hS) := by
    have he := congrArg (fun I : Finset (SourcePair S) => I.biUnion (D.couplePairBlock hS))
      (Finset.insert_erase (Finset.mem_univ p))
    rw [Finset.biUnion_insert] at he
    exact he.symm
  change Finset.univ.biUnion (D.couplePairBlock hS) ∪ _ = _
  rw [hc]
  dsimp only [ReconstructionData.coupleBackground]
  ac_rfl

theorem ReconstructionData.eraseCouple_background {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (p : SourcePair S) :
    (D.eraseCouple p).coupleBackground hS p = D.coupleBackground hS p := by
  apply congrArg (fun T => T ∪ _)
  apply Finset.biUnion_congr rfl
  intro q hq
  change (((D.eraseCouple p).couple q).pairsAt _ _).toFinset = _
  rw [D.eraseCouple_other p q (Finset.ne_of_mem_erase hq)]
  rfl

end WaveTurbulence.Reg.Skeleton
