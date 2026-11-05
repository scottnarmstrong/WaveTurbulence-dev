/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.InflationGeometry
public import WaveTurbulence.Foundations.Molecule.LFTwist.TrivialPairLeaves
public import WaveTurbulence.Foundations.Molecule.LFTwist.Prelayering
public import WaveTurbulence.Foundations.Molecule.TwistParents

/-! # The actual twist site in a reconstruction with trivial exceptional couple

The lower regular tree may be arbitrary for placement validity. LF erases it
to nil before using reconstruction–twist naturality.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist
variable {w : ℕ} {S G : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (hd : D.Decodes hS G)

theorem decodedCoreBranch_nonroot (b : GBranch S.tree) (hb : b.1.2 ≠ []) :
    (D.decodedCoreBranch hS hd b).1.2 ≠ [] := by
  intro he
  have hn := inflatedPosition_nonroot S D.tree b.toNode hb
  change (addrExt (inflatedPosition S D.tree b.toNode) (D.tree b).lonePath).2 = [] at he
  have hl := congrArg List.length he
  change ((inflatedPosition S D.tree b.toNode).2 ++ (D.tree b).lonePath).length = 0 at hl
  simp only [List.length_append] at hl
  exact hn (List.length_eq_zero_iff.mp (by omega))

/-- The actual retained core branch has its original ordered source child. -/
theorem decodedTrivLeaf_child (b : GBranch S.tree) (l : GLeaf S.tree) (i : Fin 3)
    (hl : l.toNode = b.child i) (hq : D.couple (pairOfLeaf S hS l) = .triv) :
    (decodedTrivLeaf D hS hd l hq).toNode = (D.decodedCoreBranch hS hd b).child i := by
  apply Subtype.ext
  exact (congrArg (inflatedPosition S D.tree) hl).trans (D.core_child_position b i)

/-- The paired endpoint's parent is exactly its original parent's retained core branch. -/
theorem decodedTrivLeaf_parent (l : GLeaf S.tree) (hl : l.1.2 ≠ [])
    (hq : D.couple (pairOfLeaf S hS l) = .triv) :
    GNode.parent (decodedTrivLeaf D hS hd l hq).toNode (inflatedPosition_nonroot S D.tree l.toNode hl) =
      D.decodedCoreBranch hS hd (GNode.parent l.toNode hl) := by
  apply parent_eq_of_child
  exact decodedTrivLeaf_child D hS hd _ l _ (child_parent l.toNode hl).symm hq

/-- Every skeleton core placement lifts to a literal actual placement once its
exceptional pair has been erased to the trivial couple. -/
@[expose] noncomputable def expandedPlacement (P : CorePlacement S)
    (hq : D.couple (pairOfLeaf S hS P.retained) = .triv) : CorePlacement G where
  lower := D.decodedCoreBranch hS hd P.lower
  retained := decodedTrivLeaf D hS hd P.retained hq
  nonroot := decodedCoreBranch_nonroot D hS hd P.lower P.nonroot
  paired_nonroot := by
    have hp := decodedTrivLeaf_pair D hS hd P.retained hq
    rw [hp]
    exact inflatedPosition_nonroot S D.tree (S.pair P.retained).toNode P.paired_nonroot
  keep := P.keep
  unmarked := hd.1 _
  child := decodedTrivLeaf_child D hS hd P.lower P.retained P.keep P.child hq
  outer := P.outer
  paired_outside := by
    intro hdesc
    have hp := decodedTrivLeaf_pair D hS hd P.retained hq
    rw [hp] at hdesc
    have hpre : Below (inflatedPosition S D.tree P.lower.toNode) (D.corePosition P.lower) :=
      ⟨rfl,List.prefix_append _ _⟩
    have htail : Below (D.corePosition P.lower) (inflatedPosition S D.tree (S.pair P.retained).toNode) :=
      ⟨hdesc.1.symm,hdesc.2⟩
    have hfull : Below (inflatedPosition S D.tree P.lower.toNode)
        (inflatedPosition S D.tree (S.pair P.retained).toNode) :=
      ⟨htail.1.trans hpre.1,hpre.2.trans htail.2⟩
    have hs := (inflatedPosition_below_iff S D.tree P.lower.toNode (S.pair P.retained).toNode).mp hfull
    exact P.paired_outside ⟨hs.1.symm,hs.2⟩

end WaveTurbulence.LFTwist
