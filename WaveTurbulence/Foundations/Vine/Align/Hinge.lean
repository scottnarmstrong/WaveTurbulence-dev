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
      (batchMolIso hr.batch).e ((stSt S σ).M.ob c) := by
  let h := batchMolIso_spec hr.batch
  let e := (h.spliceMolIso σ (unitsFamily_isV0Fam hM σ)).e
  calc
    _ = (endpointShape hM σ D hS layer hLayer hr hn).br (e c) := by
      exact (congrArg (commonShape hM σ D hS layer hLayer hr hn).br
        (h.splice_branch_cast σ (unitsFamily_isV0Fam hM σ) c).symm).trans
          (castShape_br (h.splice_garden_eq σ (unitsFamily_isV0Fam hM σ))
            (endpointShape hM σ D hS layer hLayer hr hn) (e c))
    _ = (stSt Y.skeleton (transportPrescription (batchMolIso hr.batch) σ)).M.ob (e c) := by
      unfold endpointShape
      rw [congrBlocks_br]
      rfl
    _ = _ := h.spliceMolIso_branch_names σ (unitsFamily_isV0Fam hM σ) c

/-- Each labelled hinge, not just their finite set, is class-independent. -/
theorem commonShape_hinge (j : Fin (unitBlocks S σ).length) :
    (commonShape hM σ D hS layer hLayer hr hn).hinge (member_disj hM σ D hS layer hLayer hr hn) j =
      (stShape hM σ).hinge (unitBlk_disj hM σ) j := by
  classical
  apply (commonShape hM σ D hS layer hLayer hr hn).br_inj
  rw [SpliceShape.br_hinge, commonShape_br]
  have hc := (reachU_coordinates hr hn (batchMolIso_spec hr.batch) j).2.1
  exact hc.trans (congrArg (batchMolIso hr.batch).e ((stShape hM σ).br_hinge (unitBlk_disj hM σ) j).symm)

/-- Slot zero of the momentum boundary is the same common hinge node. -/
theorem commonShape_hmom_zero (j : Fin (unitBlocks S σ).length) :
    (commonShape hM σ D hS layer hLayer hr hn).hmom (member_disj hM σ D hS layer hLayer hr hn) j 0 =
      (stShape hM σ).hmom (unitBlk_disj hM σ) j 0 := by
  rw [SpliceShape.hmom_zero, SpliceShape.hmom_zero, commonShape_hinge]

/-- The upper clock of each unit is literally common to every class member. -/
theorem commonShape_hclk_zero (j : Fin (unitBlocks S σ).length) :
    (commonShape hM σ D hS layer hLayer hr hn).hclk (member_disj hM σ D hS layer hLayer hr hn) j 0 =
      (stShape hM σ).hclk (unitBlk_disj hM σ) j 0 := by
  change Sum.inr _ = Sum.inr _
  exact congrArg Sum.inr (commonShape_hinge hM σ D hS layer hLayer hr hn j)

end WaveTurbulence.VineAlign
