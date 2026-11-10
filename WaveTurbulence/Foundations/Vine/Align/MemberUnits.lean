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

section MemberUnitsMk
/-! B1b-3: the member-unit chain at a marking `Mk` of the start skeleton. A class member `Y` carries its own marking
`Mk'`, transported along its actual batch (`MarkTransported (batchMolIso hr.batch) Mk Mk'`). -/
variable {w p : ℕ} {kind : Bool} {S : Garden w}
  (hM : S.molecule.IsMolecule) (σ : Prescription S) {Mk : Set (CLVine S)}
  (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)

variable {Y : FamilyReconstruction w (UnitsIndex (alignedAssemblyMk hM σ Mk))}
  {vs : ∀ j, UnitAt Y.skeleton Y.family ((unitsSplit (alignedAssemblyMk hM σ Mk)).Q j)}
  {L : List (UnitsIndex (alignedAssemblyMk hM σ Mk))}
  (hr : ReachU p kind (unitsSplit (alignedAssemblyMk hM σ Mk)).Q L
    (unitsStart (alignedAssemblyMk hM σ Mk) (unitBlkMk_disj hM σ Mk) D hS layer hLayer)
    (unitsRegion (alignedAssemblyMk hM σ Mk) (unitBlkMk_disj hM σ Mk)) Y vs)
  (hn : L.Nodup)

include hn

/-- B1b-3 (Mk-general form of `member_unit_atoms`). -/
theorem member_unit_atomsMk (j : Fin (unitBlocks S σ Mk).length) :
    (unitClBlock (vs j)).atoms = (batchMolIso hr.batch).img (unitBlkMk hM σ Mk j).atoms := by
  classical
  exact (reachU_coordinates hr hn (batchMolIso_spec hr.batch) j).1

/-- B1b-3 (Mk-general form of `member_unit_mem`): each carried unit is an endpoint unit at the member's marking. -/
theorem member_unit_memMk {Mk' : Set (CLVine Y.skeleton)}
    (hT : Stage1Mk.MarkTransported (batchMolIso hr.batch) Mk Mk') (j : Fin (unitBlocks S σ Mk).length) :
    unitClBlock (vs j) ∈ unitBlocks Y.skeleton (transportPrescription (batchMolIso hr.batch) σ) Mk' := by
  have hu := List.get_mem (unitBlocks S σ Mk) j
  obtain ⟨v, hv, ha, _, _⟩ := (batchMolIso_spec hr.batch).units_jointsMk σ hT (unitsFamily_isV0FamMk hM σ) hu
  have he : unitClBlock (vs j) = v := clBlock_eq_of_atoms
    ((member_unit_atomsMk hM σ D hS layer hLayer hr hn j).trans ha.symm)
  exact he.symm ▸ hv

/-- B1b-3 (Mk-general form of `member_units_bijective`). -/
theorem member_units_bijectiveMk {Mk' : Set (CLVine Y.skeleton)}
    (hT : Stage1Mk.MarkTransported (batchMolIso hr.batch) Mk Mk') :
    Function.Bijective (fun j : Fin (unitBlocks S σ Mk).length =>
      (⟨unitClBlock (vs j), member_unit_memMk hM σ D hS layer hLayer hr hn hT j⟩ :
        {u : CLBlock Y.skeleton // u ∈ unitBlocks Y.skeleton (transportPrescription (batchMolIso hr.batch) σ) Mk'})) := by
  classical
  constructor
  · intro j k he
    apply (VineA.unitBlocks_nodupMk σ).injective_get
    apply clBlock_eq_of_atoms
    apply (batchMolIso hr.batch).img_injective
    exact (member_unit_atomsMk hM σ D hS layer hLayer hr hn j).symm.trans
      ((congrArg (fun u => u.1.atoms) he).trans (member_unit_atomsMk hM σ D hS layer hLayer hr hn k))
  · intro u
    have hm := (batchMolIso_spec hr.batch).unitsMk σ Mk Mk' (unitsFamily_isV0FamMk hM σ) hT
    have hx := hm.mem_iff.mpr (List.mem_map.mpr ⟨u.1, u.2, rfl⟩)
    obtain ⟨v, hv, ha⟩ := List.mem_map.mp hx
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hv
    refine ⟨j, Subtype.ext (clBlock_eq_of_atoms ?_)⟩
    exact (member_unit_atomsMk hM σ D hS layer hLayer hr hn j).trans ha

/-- B1b-3 (Mk-general form of `memberUnitIndex`). -/
noncomputable def memberUnitIndexMk {Mk' : Set (CLVine Y.skeleton)}
    (hT : Stage1Mk.MarkTransported (batchMolIso hr.batch) Mk Mk') : Fin (unitBlocks S σ Mk).length ≃
    Fin (unitBlocks Y.skeleton (transportPrescription (batchMolIso hr.batch) σ) Mk').length := by
  classical
  exact (Equiv.ofBijective _ (member_units_bijectiveMk hM σ D hS layer hLayer hr hn hT)).trans
    (List.Nodup.getEquiv _ (VineA.unitBlocks_nodupMk _)).symm

/-- B1b-3 (Mk-general form of `memberUnitIndex_block`). -/
theorem memberUnitIndex_blockMk {Mk' : Set (CLVine Y.skeleton)}
    (hT : Stage1Mk.MarkTransported (batchMolIso hr.batch) Mk Mk') (j : Fin (unitBlocks S σ Mk).length) :
    unitBlkMk (Mole.garden_isMolecule Y.skeleton) (transportPrescription (batchMolIso hr.batch) σ) Mk'
      (memberUnitIndexMk hM σ D hS layer hLayer hr hn hT j) = unitClBlock (vs j) := by
  classical
  exact congrArg Subtype.val ((List.Nodup.getEquiv _ (VineA.unitBlocks_nodupMk _)).apply_symm_apply _)

end MemberUnitsMk

variable {w p : ℕ} {kind : Bool} {S : Garden w}
  (hM : S.molecule.IsMolecule) (σ : Prescription S)
  (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)

variable {Y : FamilyReconstruction w (UnitsIndex (alignedAssembly hM σ))}
  {vs : ∀ j, UnitAt Y.skeleton Y.family ((unitsSplit (alignedAssembly hM σ)).Q j)}
  {L : List (UnitsIndex (alignedAssembly hM σ))}
  (hr : ReachU p kind (unitsSplit (alignedAssembly hM σ)).Q L
    (unitsStart (alignedAssembly hM σ) (unitBlk_disj hM σ) D hS layer hLayer)
    (unitsRegion (alignedAssembly hM σ) (unitBlk_disj hM σ)) Y vs)
  (hn : L.Nodup)

include hn

/-- Each carried unit is literally an endpoint producer unit. -/
theorem member_unit_mem (j : Fin (unitBlocks S σ).length) :
    unitClBlock (vs j) ∈ unitBlocks Y.skeleton (transportPrescription (batchMolIso hr.batch) σ) :=
  member_unit_memMk hM σ D hS layer hLayer hr hn (Stage1Mk.markTransported_empty _) j

/-- The carried units enumerate the endpoint units bijectively. -/
theorem member_units_bijective :
    Function.Bijective (fun j : Fin (unitBlocks S σ).length =>
      (⟨unitClBlock (vs j), member_unit_mem hM σ D hS layer hLayer hr hn j⟩ :
        {u : CLBlock Y.skeleton // u ∈ unitBlocks Y.skeleton (transportPrescription (batchMolIso hr.batch) σ)})) :=
  member_units_bijectiveMk hM σ D hS layer hLayer hr hn (Stage1Mk.markTransported_empty _)

/-- Exact common-unit to endpoint-unit index equivalence. -/
noncomputable def memberUnitIndex : Fin (unitBlocks S σ).length ≃
    Fin (unitBlocks Y.skeleton (transportPrescription (batchMolIso hr.batch) σ)).length := by
  classical
  exact (Equiv.ofBijective _ (member_units_bijective hM σ D hS layer hLayer hr hn)).trans
    (List.Nodup.getEquiv _ (VineA.unitBlocks_nodup _)).symm

/-- The index equivalence identifies the whole carried CL block. -/
theorem memberUnitIndex_block (j : Fin (unitBlocks S σ).length) :
    unitBlk (Mole.garden_isMolecule Y.skeleton) (transportPrescription (batchMolIso hr.batch) σ)
      (memberUnitIndex hM σ D hS layer hLayer hr hn j) = unitClBlock (vs j) :=
  memberUnitIndex_blockMk hM σ D hS layer hLayer hr hn (Stage1Mk.markTransported_empty _) j

end WaveTurbulence.VineAlign
