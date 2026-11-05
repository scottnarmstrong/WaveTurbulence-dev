/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.ExpandedLayers
public import WaveTurbulence.Foundations.Molecule.TypeIParent
public import WaveTurbulence.Foundations.Molecule.TypeIILowerParent

/-! # The printed vine eligibility inequalities imply the uniform parent guard

Type I needs no extra layer guard. Type II uses the printed minimum of the
two actual adjacent rung-atom layers, including the one-rung vine.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist
variable {w : ℕ} (S : Garden w) (P : CorePlacement S)

/-- In type I the paired retained leaf's parent is the upper joint. -/
theorem typeI_paired_parent {B : Finset (GBranch S.tree)} {a : GBranch S.tree}
    (hV : S.molecule.IsVine .I B a P.lower) (hP : IsPlacementAt S B P.lower P) :
    GNode.parent (S.pair P.retained).toNode P.paired_nonroot = a := by
  have hp := paired_parent_selected P hP
  rw [Molecpl.typeI_atoms S.molecule hV] at hp
  rcases Finset.mem_insert.mp hp with he | he
  · exact he
  · have he := Finset.mem_singleton.mp he
    have hd : (GNode.parent (S.pair P.retained).toNode P.paired_nonroot).toNode.IsDesc
        (S.pair P.retained).toNode := ⟨rfl,List.dropLast_prefix _⟩
    rw [he] at hd
    exact (P.paired_outside hd).elim

/-- The printed absence of a type-I guard is justified by branch monotonicity. -/
theorem typeI_induced_parent_guard {B : Finset (GBranch S.tree)} {a : GBranch S.tree}
    (LG : LayeredGarden w) (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS LG.garden)
    (hV : S.molecule.IsVine .I B a P.lower) (hCL : Mole.CLParentPattern S B a P.lower)
    (hP : IsPlacementAt S B P.lower P) :
    inducedPrelayer LG D hS hd P.lower ≤
      inducedPrelayer LG D hS hd (GNode.parent (S.pair P.retained).toNode P.paired_nonroot) := by
  obtain ⟨i,hi⟩ := Molecpl.typeI_child S hV hCL
  exact (inducedPrelayer_isBranchPrelayering LG D hS hd a P.lower i hi.symm).trans_eq
    (congrArg (inducedPrelayer LG D hS hd) (typeI_paired_parent S P hV hP)).symm

/-- In type II the paired retained leaf's parent is one of the two adjacent rung atoms. -/
theorem typeII_paired_parent {B : Finset (GBranch S.tree)} {a : GBranch S.tree}
    (hB : S.molecule.IsBlock B a P.lower) (R : Molecpl.EndRungData S.molecule B a P.lower)
    (hP : IsPlacementAt S B P.lower P) :
    GNode.parent (S.pair P.retained).toNode P.paired_nonroot = R.left ∨
      GNode.parent (S.pair P.retained).toNode P.paired_nonroot = R.right := by
  have ha : S.molecule.atom (retainedLP S P) = P.lower := retained_parent S P
  have hg : S.molecule.InGroup B (retainedLP S P) := by
    constructor
    · rw [ha]
      exact hB.2.2.1
    · exact paired_parent_selected P hP
  exact R.lower_neighbor hB ha hg

/-- The printed type-II minimum bound gives precisely the uniform guard. -/
theorem typeII_induced_parent_guard {B : Finset (GBranch S.tree)} {a : GBranch S.tree}
    (LG : LayeredGarden w) (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS LG.garden)
    (hB : S.molecule.IsBlock B a P.lower) (R : Molecpl.EndRungData S.molecule B a P.lower)
    (hP : IsPlacementAt S B P.lower P)
    (hb : inducedPrelayer LG D hS hd P.lower ≤
      min (inducedPrelayer LG D hS hd R.left) (inducedPrelayer LG D hS hd R.right)) :
    inducedPrelayer LG D hS hd P.lower ≤
      inducedPrelayer LG D hS hd (GNode.parent (S.pair P.retained).toNode P.paired_nonroot) := by
  rcases typeII_paired_parent S P hB R hP with he | he
  · exact (hb.trans (min_le_left _ _)).trans_eq (congrArg (inducedPrelayer LG D hS hd) he).symm
  · exact (hb.trans (min_le_right _ _)).trans_eq (congrArg (inducedPrelayer LG D hS hd) he).symm

end WaveTurbulence.LFTwist
