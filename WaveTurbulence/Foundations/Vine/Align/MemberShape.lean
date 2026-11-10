/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.Align.MemberUnits
public import WaveTurbulence.Foundations.Vine.Align.Shape
/-! Shapes on the common garden, indexed by the actual VINE-C carried units. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineAlign
open VineEstS4 VineA VineB VineC RedSplice Stage1 Twist RegRed Represents LFTwist Reg.Skeleton

section MemberShapeMk
/-! B1b-3: member shapes at a marking `Mk`; the member's own marking `Mk'` is carried by its batch. -/
variable {w p : ℕ} {kind : Bool} {S : Garden w}
  (hM : S.molecule.IsMolecule) (σ : Prescription S) {Mk : Set (CLVine S)}
  (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  {Y : FamilyReconstruction w (UnitsIndex (alignedAssemblyMk hM σ Mk))}
  {vs : ∀ j, UnitAt Y.skeleton Y.family ((unitsSplit (alignedAssemblyMk hM σ Mk)).Q j)}
  {L : List (UnitsIndex (alignedAssemblyMk hM σ Mk))}
  (hr : ReachU p kind (unitsSplit (alignedAssemblyMk hM σ Mk)).Q L
    (unitsStart (alignedAssemblyMk hM σ Mk) (unitBlkMk_disj hM σ Mk) D hS layer hLayer)
    (unitsRegion (alignedAssemblyMk hM σ Mk) (unitBlkMk_disj hM σ Mk)) Y vs)
  (hn : L.Nodup)

include hr hn

/-- B1b-3 (Mk-general form of `member_disj`; no member marking is needed). -/
theorem member_disjMk : Disj (fun j => unitClBlock (vs j)) := by
  classical
  intro j k hjk
  rw [member_unit_atomsMk hM σ D hS layer hLayer hr hn j, member_unit_atomsMk hM σ D hS layer hLayer hr hn k]
  exact (Finset.disjoint_image (batchMolIso hr.batch).e.injective).mpr (unitBlkMk_disj hM σ Mk j k hjk)

/-- B1b-3 (Mk-general form of `endpointShape`): the endpoint's own `stShape` at its marking `Mk'`. -/
noncomputable def endpointShapeMk {Mk' : Set (CLVine Y.skeleton)}
    (hT : Stage1Mk.MarkTransported (batchMolIso hr.batch) Mk Mk') : SpliceShape (fun j => unitClBlock (vs j))
    (stSt Y.skeleton (transportPrescription (batchMolIso hr.batch) σ) Mk').G :=
  congrBlocks (funext (memberUnitIndex_blockMk hM σ D hS layer hLayer hr hn hT))
    (reindexShape (stShape (Mole.garden_isMolecule Y.skeleton) (transportPrescription (batchMolIso hr.batch) σ) Mk')
      (memberUnitIndexMk hM σ D hS layer hLayer hr hn hT))

/-- B1b-3 (Mk-general form of `commonShape`): every member has a shape on the representative's `G_sb` at `Mk`. -/
noncomputable def commonShapeMk {Mk' : Set (CLVine Y.skeleton)}
    (hT : Stage1Mk.MarkTransported (batchMolIso hr.batch) Mk Mk') :
    SpliceShape (fun j => unitClBlock (vs j)) (stSt S σ Mk).G :=
  castShape ((batchMolIso_spec hr.batch).splice_garden_eqMk σ hT (unitsFamily_isV0FamMk hM σ))
    (endpointShapeMk hM σ D hS layer hLayer hr hn hT)

/-- B1b-3 (Mk-general form of `endpointShape_hinges`). -/
theorem endpointShape_hingesMk {Mk' : Set (CLVine Y.skeleton)}
    (hT : Stage1Mk.MarkTransported (batchMolIso hr.batch) Mk Mk') :
    (endpointShapeMk hM σ D hS layer hLayer hr hn hT).hinges (member_disjMk hM σ D hS layer hLayer hr hn) =
      (stSt Y.skeleton (transportPrescription (batchMolIso hr.batch) σ) Mk').hinges := by
  classical
  unfold endpointShapeMk
  rw [congrBlocks_hinges _ _
    (reindex_disj (unitBlkMk_disj (Mole.garden_isMolecule Y.skeleton)
      (transportPrescription (batchMolIso hr.batch) σ) Mk') _) _]
  rw [reindexShape_hinges _ (unitBlkMk_disj (Mole.garden_isMolecule Y.skeleton)
    (transportPrescription (batchMolIso hr.batch) σ) Mk'), stShape_hingesMk]

/-- B1b-3 (Mk-general form of `commonShape_hinges`): R-HINGE at a marking. -/
theorem commonShape_hingesMk {Mk' : Set (CLVine Y.skeleton)}
    (hT : Stage1Mk.MarkTransported (batchMolIso hr.batch) Mk Mk') :
    (commonShapeMk hM σ D hS layer hLayer hr hn hT).hinges (member_disjMk hM σ D hS layer hLayer hr hn) =
      (stSt S σ Mk).hinges := by
  let h := batchMolIso_spec hr.batch
  have hh := (batchMolIso_spec hr.batch).splice_hinges_imageMk σ hT (unitsFamily_isV0FamMk (Mk := Mk) hM σ)
  refine (castShape_hinges (h.splice_garden_eqMk σ hT (unitsFamily_isV0FamMk (Mk := Mk) hM σ))
    (endpointShapeMk hM σ D hS layer hLayer hr hn hT) (member_disjMk hM σ D hS layer hLayer hr hn)).trans ?_
  rw [endpointShape_hingesMk, ← hh]
  erw [Finset.image_image]
  have he : (fun b => gardenBranchCast (h.splice_garden_eqMk σ hT (unitsFamily_isV0FamMk (Mk := Mk) hM σ))
      ((h.spliceMolIsoMk σ hT (unitsFamily_isV0FamMk (Mk := Mk) hM σ)).e b)) = id :=
    funext (h.splice_branch_castMk σ hT (unitsFamily_isV0FamMk (Mk := Mk) hM σ))
  exact (congrArg (fun f : GBranch (stSt S σ Mk).G.tree → GBranch (stSt S σ Mk).G.tree =>
    Finset.image f (stSt S σ Mk).hinges) he).trans Finset.image_id

end MemberShapeMk

variable {w p : ℕ} {kind : Bool} {S : Garden w}
  (hM : S.molecule.IsMolecule) (σ : Prescription S)
  (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  {Y : FamilyReconstruction w (UnitsIndex (alignedAssembly hM σ))}
  {vs : ∀ j, UnitAt Y.skeleton Y.family ((unitsSplit (alignedAssembly hM σ)).Q j)}
  {L : List (UnitsIndex (alignedAssembly hM σ))}
  (hr : ReachU p kind (unitsSplit (alignedAssembly hM σ)).Q L
    (unitsStart (alignedAssembly hM σ) (unitBlk_disj hM σ) D hS layer hLayer)
    (unitsRegion (alignedAssembly hM σ) (unitBlk_disj hM σ)) Y vs)
  (hn : L.Nodup)

include hr hn

/-- The actual carried unit blocks remain disjoint. -/
theorem member_disj : Disj (fun j => unitClBlock (vs j)) := member_disjMk hM σ D hS layer hLayer hr hn

/-- The endpoint's own `stShape`, with the exact common unit index. -/
noncomputable def endpointShape : SpliceShape (fun j => unitClBlock (vs j))
    (stSt Y.skeleton (transportPrescription (batchMolIso hr.batch) σ)).G :=
  congrBlocks (funext (memberUnitIndex_block hM σ D hS layer hLayer hr hn))
    (reindexShape (stShape (Mole.garden_isMolecule Y.skeleton) (transportPrescription (batchMolIso hr.batch) σ))
      (memberUnitIndex hM σ D hS layer hLayer hr hn))

/-- Every actual class member has a shape on the representative's literal G_sb. -/
noncomputable def commonShape : SpliceShape (fun j => unitClBlock (vs j)) (stSt S σ).G :=
  castShape ((batchMolIso_spec hr.batch).splice_garden_eq σ (unitsFamily_isV0Fam hM σ))
    (endpointShape hM σ D hS layer hLayer hr hn)

end WaveTurbulence.VineAlign
