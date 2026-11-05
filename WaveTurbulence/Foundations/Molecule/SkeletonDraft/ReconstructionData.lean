/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionPositions
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.PairPartition

/-! # Literal regular-tree and regular-couple assignments at actual skeleton slots -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

abbrev SourcePair {w : ℕ} (S : Garden w) := {p : Pair w // p ∈ sourcePairs S}

/-- One regular tree at every actual branch and one regular couple at every actual leaf pair. -/
structure ReconstructionData {w : ℕ} (S : Garden w) where
  tree : GBranch S.tree → RegChain
  couple : SourcePair S → RegCpl
  tree_wf : ∀ b, (tree b).wf = true
  couple_wf : ∀ p, (couple p).wf = true

/-- Identity replacement data, including the trivial regular tree at each branch. -/
def ReconstructionData.identity {w : ℕ} (S : Garden w) : ReconstructionData S where
  tree := fun _ => .nil
  couple := fun _ => .triv
  tree_wf := fun _ => rfl
  couple_wf := fun _ => rfl

/-- The unique oriented source pair incident to a particular actual leaf. -/
def pairOfLeaf {w : ℕ} (S : Garden w) (hS : S.IsPlain) (ℓ : GLeaf S.tree) : SourcePair S :=
  ⟨sourcePairAt S ℓ,sourcePairAt_mem S hS ℓ⟩

theorem pairOfLeaf_partner {w : ℕ} (S : Garden w) (hS : S.IsPlain) (ℓ : GLeaf S.tree) :
    pairOfLeaf S hS (S.pair ℓ) = pairOfLeaf S hS ℓ :=
  Subtype.ext (sourcePairAt_pair S hS ℓ)

/-- The tree inserted at a source leaf is the corresponding sign side of its shared couple code. -/
def ReconstructionData.leafTree {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (ℓ : GLeaf S.tree) : TTree :=
  treeOfSign (D.couple (pairOfLeaf S hS ℓ)).trees (nodeSign S.sig ℓ.1)

/-- The positive endpoint of a canonical source pair is an actual source leaf. -/
def SourcePair.firstLeaf {w : ℕ} {S : Garden w} (p : SourcePair S) (hS : S.IsPlain) : GLeaf S.tree :=
  ⟨p.1.1,((rawOfGarden_valid S hS).1 p.1 p.2).1⟩

/-- The negative endpoint of a canonical source pair is an actual source leaf. -/
def SourcePair.secondLeaf {w : ℕ} {S : Garden w} (p : SourcePair S) (hS : S.IsPlain) : GLeaf S.tree :=
  ⟨p.1.2,((rawOfGarden_valid S hS).1 p.1 p.2).2.1⟩

/-- Literal framed internal matching of every regular replacement, without any enumeration convention. -/
noncomputable def ReconstructionData.attachmentPairs {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) : Finset (Pair w) :=
  Finset.univ.biUnion (fun p : SourcePair S =>
    ((D.couple p).pairsAt (inflatedPosition S D.tree (p.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (p.secondLeaf hS).toNode)).toFinset) ∪
  Finset.univ.biUnion (fun b : GBranch S.tree =>
    ((D.tree b).pairsAt (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode)).toFinset)

end WaveTurbulence.Reg.Skeleton
