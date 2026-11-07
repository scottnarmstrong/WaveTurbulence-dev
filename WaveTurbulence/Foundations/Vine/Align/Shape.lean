/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.B.Fold8
public import WaveTurbulence.Foundations.Vine.A.VineFullA4
/-! Structural transport of the actual splice shape. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineAlign
open VineB VineA RedSplice
variable {w : ℕ} {S G H : Garden w} {J K : Type} {blk : J → CLBlock S}

/-- Transport a splice shape along literal target-garden equality. -/
def castShape (h : G = H) (Φ : SpliceShape blk G) : SpliceShape blk H := h ▸ Φ

/-- Change only the enumeration of units in a shape. -/
noncomputable def reindexShape (Φ : SpliceShape blk G) (e : K ≃ J) :
    SpliceShape (fun k => blk (e k)) G where
  node := Φ.node
  inj := Φ.inj
  range x := by
    rw [Φ.range]
    exact ⟨fun h k => h (e k), fun h j => by simpa only [e.apply_symm_apply] using h (e.symm j)⟩
  tree_eq := Φ.tree_eq
  root := Φ.root
  br := Φ.br
  br_node := Φ.br_node
  leaf := Φ.leaf
  leaf_node := Φ.leaf_node
  child c i h := Φ.child c i (fun j => by simpa only [e.apply_symm_apply] using h (e.symm j))
  crown c k h := Φ.crown c (e k) h
  pair := Φ.pair
  sign := Φ.sign

/-- Disjointness survives a unit-index equivalence. -/
theorem reindex_disj (hd : Disj blk) (e : K ≃ J) : Disj (fun k => blk (e k)) :=
  fun k l h => hd (e k) (e l) (fun he => h (e.injective he))

/-- Reindexing does not change the actual hinge set. -/
theorem reindexShape_hinges [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
    (Φ : SpliceShape blk G) (hd : Disj blk) (e : K ≃ J) :
    (reindexShape Φ e).hinges (reindex_disj hd e) = Φ.hinges hd := by
  ext c
  rw [SpliceShape.mem_hinges, SpliceShape.mem_hinges]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨e k, hk⟩
  · rintro ⟨j, hj⟩
    refine ⟨e.symm j, ?_⟩
    simpa only [reindexShape, e.apply_symm_apply] using hj

/-- Transport the same shape after identifying its complete unit function. -/
def congrBlocks {blk' : J → CLBlock S} (h : blk = blk')
    (Φ : SpliceShape blk G) : SpliceShape blk' G := h ▸ Φ

/-- Changing a unit-function expression preserves its hinge set. -/
theorem congrBlocks_hinges [Fintype J] [DecidableEq J] {blk' : J → CLBlock S}
    (h : blk = blk') (Φ : SpliceShape blk G) (hd : Disj blk) (hd' : Disj blk') :
    (congrBlocks h Φ).hinges hd' = Φ.hinges hd := by
  subst blk'
  rfl

/-- Literal target transport carries exactly the same hinges. -/
theorem castShape_hinges [Fintype J] [DecidableEq J] (h : G = H)
    (Φ : SpliceShape blk G) (hd : Disj blk) :
    (castShape h Φ).hinges hd = (Φ.hinges hd).image (gardenBranchCast h) := by
  subst H
  exact Finset.image_id.symm

/-- The branch map under a target cast uses the exact garden-equality cast. -/
theorem castShape_br (h : G = H) (Φ : SpliceShape blk G) (c : GBranch G.tree) :
    (castShape h Φ).br (gardenBranchCast h c) = Φ.br c := by
  subst H
  rfl

/-- Rewriting the unit function leaves the actual old-branch map unchanged. -/
theorem congrBlocks_br {blk' : J → CLBlock S} (h : blk = blk') (Φ : SpliceShape blk G) :
    (congrBlocks h Φ).br = Φ.br := by
  subst blk'
  rfl

/-- A representative's actual shape, on its literal exported garden. -/
noncomputable def profileShape {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) :
    SpliceShape (unitBlk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma)
      a.fullProfile.piece.gap.garden :=
  stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma

/-- Every prescribed member has a shape onto the same literal profile garden. -/
noncomputable def memberShape {R p : ℕ} {kind : Bool}
    (a b : PrescribedPrimeGarden (2 * R)) (hσ : b.code = a.code)
    (hy : b.layered ∈ a.outputs (p := p) (kind := kind)) :
    SpliceShape (unitBlk (Mole.garden_isMolecule b.prime.skeleton) b.totalSigma)
      a.fullProfile.piece.gap.garden :=
  castShape (congrArg (fun P : FullA4Profile (2 * R) => P.piece.gap.garden)
    (PrescribedPrimeGarden.plainTau_fullA4 hσ hy)) (profileShape b)

/-- The shape's hinge set is exactly the successor producer's hinge set. -/
theorem profileShape_hinges {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) :
    (profileShape a).hinges (unitBlk_disj (Mole.garden_isMolecule _) a.totalSigma) =
      a.fullProfile.piece.hinges :=
  stShape_hinges (Mole.garden_isMolecule _) a.totalSigma

end WaveTurbulence.VineAlign
