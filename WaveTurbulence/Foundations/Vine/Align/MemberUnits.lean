/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.Align.Coordinates
public import WaveTurbulence.Foundations.Vine.Align.Units
public import Mathlib.Data.List.NodupEquivFin
/-! Every carried unit is an actual endpoint unit, with an exact index equivalence. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineAlign
open VineEstS4 VineA VineB VineC RedSplice Stage1 Twist RegRed Represents LFTwist Reg.Skeleton
variable {w p : ℕ} {kind : Bool} {S : Garden w}
  (hM : S.molecule.IsMolecule) (σ : Prescription S)
  (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)

/-- At the start, VINE-C's raw regions are literally the producer's unit blocks. -/
theorem unitsRegion_clBlock (j : Fin (unitBlocks S σ).length) :
    unitClBlock (unitsRegion (alignedAssembly hM σ) (unitBlk_disj hM σ) j) = unitBlk hM σ j := rfl

variable {Y : FamilyReconstruction w (UnitsIndex (alignedAssembly hM σ))}
  {vs : ∀ j, UnitAt Y.skeleton Y.family ((unitsSplit (alignedAssembly hM σ)).Q j)}
  {L : List (UnitsIndex (alignedAssembly hM σ))}
  (hr : ReachU p kind (unitsSplit (alignedAssembly hM σ)).Q L
    (unitsStart (alignedAssembly hM σ) (unitBlk_disj hM σ) D hS layer hLayer)
    (unitsRegion (alignedAssembly hM σ) (unitBlk_disj hM σ)) Y vs)
  (hn : L.Nodup)

include hn

/-- VINE-C's carried blocks have the actual endpoint unit atoms. -/
theorem member_unit_atoms (j : Fin (unitBlocks S σ).length) :
    (unitClBlock (vs j)).atoms = (batchMolIso hr.batch).img (unitBlk hM σ j).atoms := by
  classical
  exact (reachU_coordinates hr hn (batchMolIso_spec hr.batch) j).1

/-- Each carried unit is literally an endpoint producer unit. -/
theorem member_unit_mem (j : Fin (unitBlocks S σ).length) :
    unitClBlock (vs j) ∈ unitBlocks Y.skeleton (transportPrescription (batchMolIso hr.batch) σ) := by
  have hu := List.get_mem (unitBlocks S σ) j
  obtain ⟨v, hv, ha, _, _⟩ := (batchMolIso_spec hr.batch).units_joints σ (unitsFamily_isV0Fam hM σ) hu
  have he : unitClBlock (vs j) = v := clBlock_eq_of_atoms
    ((member_unit_atoms hM σ D hS layer hLayer hr hn j).trans ha.symm)
  exact he.symm ▸ hv

/-- The carried units enumerate the endpoint units bijectively. -/
theorem member_units_bijective :
    Function.Bijective (fun j : Fin (unitBlocks S σ).length =>
      (⟨unitClBlock (vs j), member_unit_mem hM σ D hS layer hLayer hr hn j⟩ :
        {u : CLBlock Y.skeleton // u ∈ unitBlocks Y.skeleton (transportPrescription (batchMolIso hr.batch) σ)})) := by
  classical
  constructor
  · intro j k he
    apply (VineA.unitBlocks_nodup σ).injective_get
    apply clBlock_eq_of_atoms
    apply (batchMolIso hr.batch).img_injective
    exact (member_unit_atoms hM σ D hS layer hLayer hr hn j).symm.trans
      ((congrArg (fun u => u.1.atoms) he).trans (member_unit_atoms hM σ D hS layer hLayer hr hn k))
  · intro u
    have hm := (batchMolIso_spec hr.batch).units σ (unitsFamily_isV0Fam hM σ)
    have hx := hm.mem_iff.mpr (List.mem_map.mpr ⟨u.1, u.2, rfl⟩)
    obtain ⟨v, hv, ha⟩ := List.mem_map.mp hx
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hv
    refine ⟨j, Subtype.ext (clBlock_eq_of_atoms ?_)⟩
    exact (member_unit_atoms hM σ D hS layer hLayer hr hn j).trans ha

/-- Exact common-unit to endpoint-unit index equivalence. -/
noncomputable def memberUnitIndex : Fin (unitBlocks S σ).length ≃
    Fin (unitBlocks Y.skeleton (transportPrescription (batchMolIso hr.batch) σ)).length := by
  classical
  exact (Equiv.ofBijective _ (member_units_bijective hM σ D hS layer hLayer hr hn)).trans
    (List.Nodup.getEquiv _ (VineA.unitBlocks_nodup _)).symm

/-- The index equivalence identifies the whole carried CL block. -/
theorem memberUnitIndex_block (j : Fin (unitBlocks S σ).length) :
    unitBlk (Mole.garden_isMolecule Y.skeleton) (transportPrescription (batchMolIso hr.batch) σ)
      (memberUnitIndex hM σ D hS layer hLayer hr hn j) = unitClBlock (vs j) := by
  classical
  exact congrArg Subtype.val ((List.Nodup.getEquiv _ (VineA.unitBlocks_nodup _)).apply_symm_apply _)

end WaveTurbulence.VineAlign
