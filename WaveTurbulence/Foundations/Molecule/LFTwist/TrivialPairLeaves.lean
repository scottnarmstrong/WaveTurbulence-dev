/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.ReconstructionEmbeddings
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourcePairAtSides

/-! # Actual leaves and their partners at a trivial reconstruction couple slot -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Links
variable {w : ℕ} {S G : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (hd : D.Decodes hS G)

theorem inflateNode_triv_leaf (l : GLeaf S.tree)
    (hq : D.couple (pairOfLeaf S hS l) = .triv) : D.inflateNode hS l.toNode = .leaf := by
  rw [D.inflateNode_leaf hS l, ReconstructionData.leafTree, hq]
  simp only [RegCpl.trees, treeOfSign, ite_self]

/-- The surviving source leaf is literally a target leaf when its attached couple is trivial. -/
@[expose] noncomputable def decodedTrivLeaf (l : GLeaf S.tree)
    (hq : D.couple (pairOfLeaf S hS l) = .triv) : GLeaf G.tree :=
  ⟨inflatedPosition S D.tree l.toNode, by
    have hs := (D.decoded_subtree_position hS hd l.toNode).trans
      (congrArg some (inflateNode_triv_leaf D hS l hq))
    have hl := (Comb.subtree_leaves_iff hs []).mp (Finset.mem_singleton_self [])
    simpa only [List.append_nil] using hl⟩

/-- Both source leaves of a trivial couple remain the actual target pair. -/
theorem decodedTrivLeaf_pair (l : GLeaf S.tree)
    (hq : D.couple (pairOfLeaf S hS l) = .triv) :
    G.pair (decodedTrivLeaf D hS hd l hq) =
      decodedTrivLeaf D hS hd (S.pair l) (by simpa only [pairOfLeaf_partner] using hq) := by
  let q := pairOfLeaf S hS l
  let A := inflatedPosition S D.tree (q.firstLeaf hS).toNode
  let B := inflatedPosition S D.tree (q.secondLeaf hS).toNode
  let L := decodedTrivLeaf D hS hd l hq
  let M := decodedTrivLeaf D hS hd (S.pair l) (by simpa only [pairOfLeaf_partner] using hq)
  have hp : (A,B) ∈ (D.couple q).pairsAt A B := by
    rw [show D.couple q = .triv from hq]
    exact List.mem_singleton_self _
  have hE := reconstruction_coupleEmb D hS hd q
  by_cases hs : nodeSign S.sig l.1 = 1
  · have hside := pairOfLeaf_sides_pos S hS l hs
    have ha : L.1 = A := congrArg (fun z : GLeaf S.tree => inflatedPosition S D.tree z.toNode) hside.1.symm
    have hb : B = M.1 := congrArg (fun z : GLeaf S.tree => inflatedPosition S D.tree z.toNode) hside.2
    exact Subtype.ext ((hE.pairs (A,B) hp L ha).trans hb)
  · have hside := pairOfLeaf_sides_neg S hS l hs
    have ha : M.1 = A := congrArg (fun z : GLeaf S.tree => inflatedPosition S D.tree z.toNode) hside.1.symm
    have hb : B = L.1 := congrArg (fun z : GLeaf S.tree => inflatedPosition S D.tree z.toNode) hside.2
    have he : G.pair M = L := Subtype.ext ((hE.pairs (A,B) hp M ha).trans hb)
    exact (congrArg G.pair he).symm.trans (G.pair_pair M)

end WaveTurbulence.LFTwist
