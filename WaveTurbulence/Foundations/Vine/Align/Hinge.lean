/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.Align.MemberShape
public import WaveTurbulence.Foundations.Vine.B.Src2
/-! The common shape's branch map and individually indexed hinges. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineAlign
open VineEstS4 VineA VineB VineC RedSplice Stage1 Twist RegRed Represents LFTwist Reg.Skeleton

section HingeMk
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
  {Mk' : Set (CLVine Y.skeleton)} (hT : Stage1Mk.MarkTransported (batchMolIso hr.batch) Mk Mk')

/-- B1b-3 (Mk-general form of `commonShape_br`).
The common shape uses the actual batch map on every surviving original branch. -/
theorem commonShape_brMk (c : GBranch (stSt S σ Mk).G.tree) :
    (commonShapeMk hM σ D hS layer hLayer hr hn hT).br c =
      (batchMolIso hr.batch).e ((stSt S σ Mk).M.ob c) := by
  let h := batchMolIso_spec hr.batch
  let e := (h.spliceMolIsoMk σ hT (unitsFamily_isV0FamMk hM σ)).e
  calc
    _ = (endpointShapeMk hM σ D hS layer hLayer hr hn hT).br (e c) := by
      exact (congrArg (commonShapeMk hM σ D hS layer hLayer hr hn hT).br
        (h.splice_branch_castMk σ hT (unitsFamily_isV0FamMk hM σ) c).symm).trans
          (castShape_br (h.splice_garden_eqMk σ hT (unitsFamily_isV0FamMk hM σ))
            (endpointShapeMk hM σ D hS layer hLayer hr hn hT) (e c))
    _ = (stSt Y.skeleton (transportPrescription (batchMolIso hr.batch) σ) Mk').M.ob (e c) := by
      unfold endpointShapeMk
      rw [congrBlocks_br]
      rfl
    _ = _ := h.spliceMolIso_branch_namesMk σ hT (unitsFamily_isV0FamMk hM σ) c

/-- B1b-3 (Mk-general form of `commonShape_hinge`).
Each labelled hinge, not just their finite set, is class-independent. -/
theorem commonShape_hingeMk (j : Fin (unitBlocks S σ Mk).length) :
    (commonShapeMk hM σ D hS layer hLayer hr hn hT).hinge (member_disjMk hM σ D hS layer hLayer hr hn) j =
      (stShape hM σ Mk).hinge (unitBlkMk_disj hM σ Mk) j := by
  classical
  apply (commonShapeMk hM σ D hS layer hLayer hr hn hT).br_inj
  rw [SpliceShape.br_hinge, commonShape_brMk]
  have hc := (reachU_coordinates hr hn (batchMolIso_spec hr.batch) j).2.1
  exact hc.trans (congrArg (batchMolIso hr.batch).e ((stShape hM σ Mk).br_hinge (unitBlkMk_disj hM σ Mk) j).symm)

end HingeMk

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

/-- The common shape uses the actual batch map on every surviving original branch. -/
theorem commonShape_br (c : GBranch (stSt S σ).G.tree) :
    (commonShape hM σ D hS layer hLayer hr hn).br c =
      (batchMolIso hr.batch).e ((stSt S σ).M.ob c) :=
  commonShape_brMk hM σ D hS layer hLayer hr hn (Stage1Mk.markTransported_empty _) c

end WaveTurbulence.VineAlign
