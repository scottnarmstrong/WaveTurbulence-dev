/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.Align.BoundaryOne
public import WaveTurbulence.Foundations.Vine.Align.Hinge
public import WaveTurbulence.Foundations.Vine.Align.Excluded
/-! The same excluded crown child for every actual common shape. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineAlign
open VineEstS4 VineA VineB VineC RedSplice Stage1 Twist RegRed Represents LFTwist Reg.Skeleton

/-- Ordered information absent from the bare shape structure, supplied by actual splices. -/
def HasFirstPort {w : ℕ} {S G : Garden w} {J : Type} [Fintype J] [DecidableEq J]
    {blk : J → CLBlock S} (Φ : SpliceShape blk G) (hd : Disj blk) : Prop :=
  ∀ j, Φ.hmom hd j 1 = (Φ.hinge hd j).child (regionOf (blk j)).excluded

variable {w : ℕ} {S G H : Garden w} {J K : Type} [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K] {blk : J → CLBlock S}

/-- Reindexing does not change any labelled momentum boundary node. -/
theorem reindexShape_hmom (Φ : SpliceShape blk G) (hd : Disj blk) (e : K ≃ J) (k : K) (i : Fin 4) :
    (reindexShape Φ e).hmom (reindex_disj hd e) k i = Φ.hmom hd (e k) i := by
  apply Φ.inj
  exact ((reindexShape Φ e).node_hmom (reindex_disj hd e) k i).trans (Φ.node_hmom hd (e k) i).symm

theorem reindexShape_hinge (Φ : SpliceShape blk G) (hd : Disj blk) (e : K ≃ J) (k : K) :
    (reindexShape Φ e).hinge (reindex_disj hd e) k = Φ.hinge hd (e k) := by
  apply Φ.br_inj
  exact ((reindexShape Φ e).br_hinge (reindex_disj hd e) k).trans (Φ.br_hinge hd (e k)).symm

theorem reindex_firstPort (Φ : SpliceShape blk G) (hd : Disj blk) (e : K ≃ J)
    (hp : HasFirstPort Φ hd) : HasFirstPort (reindexShape Φ e) (reindex_disj hd e) := by
  intro k
  rw [reindexShape_hmom, reindexShape_hinge]
  exact hp (e k)

theorem congrBlocks_firstPort {blk' : J → CLBlock S} (he : blk = blk')
    (Φ : SpliceShape blk G) (hd : Disj blk) (hd' : Disj blk') (hp : HasFirstPort Φ hd) :
    HasFirstPort (congrBlocks he Φ) hd' := by
  subst blk'
  exact hp

theorem castShape_firstPort (he : G = H) (Φ : SpliceShape blk G) (hd : Disj blk)
    (hp : HasFirstPort Φ hd) : HasFirstPort (castShape he Φ) hd := by
  subst H
  exact hp

variable {p : ℕ} {kind : Bool}
  (hM : S.molecule.IsMolecule) (σ : Prescription S)
  (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  {Y : FamilyReconstruction w (UnitsIndex (alignedAssembly hM σ))}
  {vs : ∀ j, UnitAt Y.skeleton Y.family ((unitsSplit (alignedAssembly hM σ)).Q j)}
  {L : List (UnitsIndex (alignedAssembly hM σ))}
  (hr : ReachU p kind (unitsSplit (alignedAssembly hM σ)).Q L
    (unitsStart (alignedAssembly hM σ) (unitBlk_disj hM σ) D hS layer hLayer)
    (unitsRegion (alignedAssembly hM σ) (unitBlk_disj hM σ)) Y vs) (hn : L.Nodup)

/-- Actual common shapes inherit the ordered first crown port from the actual endpoint splice. -/
theorem commonShape_firstPort :
    HasFirstPort (commonShape hM σ D hS layer hLayer hr hn) (member_disj hM σ D hS layer hLayer hr hn) := by
  apply castShape_firstPort
  apply congrBlocks_firstPort _ _
    (reindex_disj (unitBlk_disj (Mole.garden_isMolecule Y.skeleton)
      (transportPrescription (batchMolIso hr.batch) σ)) _)
  apply reindex_firstPort
  exact stShape_hmom_one _ _

/-- Slot one of the actual momentum boundary is common to every class member. -/
theorem commonShape_hmom_one (j : Fin (unitBlocks S σ).length) :
    (commonShape hM σ D hS layer hLayer hr hn).hmom (member_disj hM σ D hS layer hLayer hr hn) j 1 =
      (stShape hM σ).hmom (unitBlk_disj hM σ) j 1 := by
  have he := batch_unit_excluded (batchMolIso_spec hr.batch) σ (unitsFamily_isV0Fam hM σ)
    (List.get_mem (unitBlocks S σ) j) (unitClBlock (vs j)) (member_unit_atoms hM σ D hS layer hLayer hr hn j)
  exact (commonShape_firstPort hM σ D hS layer hLayer hr hn j).trans
    ((congrArg₂ GBranch.child (commonShape_hinge hM σ D hS layer hLayer hr hn j) he).trans
      (stShape_hmom_one hM σ j).symm)

end WaveTurbulence.VineAlign
