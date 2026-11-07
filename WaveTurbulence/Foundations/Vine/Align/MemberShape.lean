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
theorem member_disj : Disj (fun j => unitClBlock (vs j)) := by
  classical
  let e := memberUnitIndex hM σ D hS layer hLayer hr hn
  have he := funext (memberUnitIndex_block hM σ D hS layer hLayer hr hn)
  exact he ▸ reindex_disj (unitBlk_disj (Mole.garden_isMolecule Y.skeleton)
    (transportPrescription (batchMolIso hr.batch) σ)) e

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

/-- The endpoint shape has exactly its independently constructed hinge set. -/
theorem endpointShape_hinges :
    (endpointShape hM σ D hS layer hLayer hr hn).hinges (member_disj hM σ D hS layer hLayer hr hn) =
      (stSt Y.skeleton (transportPrescription (batchMolIso hr.batch) σ)).hinges := by
  classical
  unfold endpointShape
  rw [congrBlocks_hinges _ _
    (reindex_disj (unitBlk_disj (Mole.garden_isMolecule Y.skeleton)
      (transportPrescription (batchMolIso hr.batch) σ)) _) _]
  rw [reindexShape_hinges _ (unitBlk_disj (Mole.garden_isMolecule Y.skeleton)
    (transportPrescription (batchMolIso hr.batch) σ)), stShape_hinges]

/-- R-HINGE: all common shapes have the representative's hinge set. -/
theorem commonShape_hinges {R : ℕ} (hwidth : w = 2 * R) :
    (commonShape hM σ D hS layer hLayer hr hn).hinges (member_disj hM σ D hS layer hLayer hr hn) =
      (stSt S σ).hinges := by
  subst w
  let h := batchMolIso_spec hr.batch
  have hh := h.piece_hinges σ (unitsFamily_isV0Fam hM σ) 0
  change ((stSt S σ).hinges).image (h.spliceMolIso σ (unitsFamily_isV0Fam hM σ)).e =
    (stSt Y.skeleton (transportPrescription (batchMolIso hr.batch) σ)).hinges at hh
  refine (castShape_hinges (h.splice_garden_eq σ (unitsFamily_isV0Fam hM σ))
    (endpointShape hM σ D hS layer hLayer hr hn) (member_disj hM σ D hS layer hLayer hr hn)).trans ?_
  rw [endpointShape_hinges, ← hh]
  erw [Finset.image_image]
  have he : (fun b => gardenBranchCast (h.splice_garden_eq σ (unitsFamily_isV0Fam hM σ))
      ((h.spliceMolIso σ (unitsFamily_isV0Fam hM σ)).e b)) = id :=
    funext (h.splice_branch_cast σ (unitsFamily_isV0Fam hM σ))
  exact (congrArg (fun f : GBranch (stSt S σ).G.tree → GBranch (stSt S σ).G.tree =>
    Finset.image f (stSt S σ).hinges) he).trans Finset.image_id

end WaveTurbulence.VineAlign
