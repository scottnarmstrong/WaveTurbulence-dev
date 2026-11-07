/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VineEst.LeafOp

/-! # Leaf correspondence of a family operation (LFTWIST-LEAFMAP, step 6) -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LFTwist
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree Links
variable {w p : ℕ} {kind : Bool} {ι : Type*} {A : FamilyReconstruction w ι} {i : ι}
  (op : FamilyOperation (p := p) (kind := kind) A i)

/-- Leaves of `A` outside the two exceptional native pieces of the operation. -/
@[expose] def FamilyOperation.IsOrdLeaf (x : GLeaf A.layered.garden.tree) : Prop :=
  (A.source i op.canonical op.eligible op.treeCoherent op.coupleCoherent).IsOrdLeaf (A.dataLeaf x)

/-- Leaves of the output outside the images of the exceptional native pieces. -/
@[expose] def FamilyOperation.IsOrdLeafOut (y : GLeaf op.output.layered.garden.tree) : Prop :=
  op.construction.IsOrdLeaf (op.output.dataLeaf y)

/-- **The leaf correspondence `φ` of one family operation** (a partial bijection): `y = φ x` iff `x` lies in
an ordinary native slot and `y` has the same relative coordinates in the image slot of the output. -/
@[expose] def FamilyOperation.LeafCorr (x : GLeaf A.layered.garden.tree) (y : GLeaf op.output.layered.garden.tree) :
    Prop :=
  op.construction.OrdCorr (A.dataLeaf x) (op.output.dataLeaf y)

variable {op}
variable {x x' : GLeaf A.layered.garden.tree} {y y' : GLeaf op.output.layered.garden.tree}

theorem FamilyOperation.LeafCorr.isOrd (h : op.LeafCorr x y) : op.IsOrdLeaf x := h.isOrd_left
theorem FamilyOperation.LeafCorr.isOrdOut (h : op.LeafCorr x y) : op.IsOrdLeafOut y := h.isOrd_right

theorem FamilyOperation.exists_leafCorr (hx : op.IsOrdLeaf x) : ∃ y, op.LeafCorr x y := by
  obtain ⟨y0, hy⟩ := op.construction.exists_corr hx
  exact ⟨op.output.gardenLeaf y0, hy⟩

theorem FamilyOperation.LeafCorr.functional (h : op.LeafCorr x y) (h' : op.LeafCorr x y') : y = y' :=
  Subtype.ext (congrArg Subtype.val (LFConstruction.OrdCorr.functional op.construction h h'))

theorem FamilyOperation.LeafCorr.injective (h : op.LeafCorr x y) (h' : op.LeafCorr x' y) : x = x' :=
by
  have e := LFConstruction.OrdCorr.injective op.construction h h'
  have e2 : (A.dataLeaf x).1 = (A.dataLeaf x').1 := congrArg Subtype.val e
  exact Subtype.ext e2


theorem FamilyOperation.LeafCorr.layer (h : op.LeafCorr x y) :
    A.layered.layer x.toNode = op.output.layered.layer y.toNode := by
  have e := LFConstruction.OrdCorr.layer op.construction h
  exact (layerAt_node A.layered x.toNode).symm.trans (e.trans (layerAt_node op.output.layered y.toNode))

theorem FamilyOperation.LeafCorr.sign (h : op.LeafCorr x y) :
    A.layered.garden.sign x.toNode = op.output.layered.garden.sign y.toNode := by
  have e := LFConstruction.OrdCorr.sign op.construction h
  change nodeSign A.layered.garden.sig x.1 = nodeSign op.output.layered.garden.sig y.1
  rw [A.sig_eq, op.output.sig_eq]
  exact e

theorem FamilyOperation.LeafCorr.index (h : op.LeafCorr x y) : x.1.1 = y.1.1 :=
  LFConstruction.OrdCorr.index op.construction h

theorem FamilyOperation.LeafCorr.mem_inputLeaves (h : op.LeafCorr x y) :
    x ∈ inputLeaves A.layered.garden ↔ y ∈ inputLeaves op.output.layered.garden := by
  have hs := h.sign
  simp only [inputLeaves, Finset.mem_filter, Finset.mem_univ, true_and, hs,
    A.decodes.1 x, op.output.decodes.1 y]

theorem FamilyOperation.LeafCorr.pair (h : op.LeafCorr x y) :
    ∃ (x' : GLeaf A.layered.garden.tree) (y' : GLeaf op.output.layered.garden.tree),
      op.LeafCorr x' y' ∧ A.layered.garden.pair x = x' ∧ op.output.layered.garden.pair y = y' := by
  obtain ⟨x0, y0, hc, hx, hy⟩ := LFConstruction.OrdCorr.pair op.construction h
  refine ⟨A.gardenLeaf x0, op.output.gardenLeaf y0, hc, ?_, ?_⟩
  · apply Subtype.ext
    exact (A.pair_val x).trans (congrArg Subtype.val hx)
  · apply Subtype.ext
    exact (op.output.pair_val y).trans (congrArg Subtype.val hy)

end WaveTurbulence.LFTwist
