/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.Align.MemberShape
public import WaveTurbulence.Foundations.Vine.Align.BatchKernels
/-! R-SLOT for the actual carried-unit shape on the common garden. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineAlign
open VineEstS4 VineA VineB VineC RedSplice Stage1 Twist RegRed Represents LFTwist Reg.Skeleton LGSpine

/-- Changing only the unit-function expression preserves the slot embedding. -/
theorem congrBlocks_iota {w : ℕ} {S G : Garden w} {J : Type} [Fintype J] [DecidableEq J]
    {blk blk' : J → CLBlock S} (h : blk = blk') (Φ : SpliceShape blk G)
    (hS : S.IsPlain) (hG : G.IsPlain) : (congrBlocks h Φ).iota hS hG = Φ.iota hS hG := by
  subst blk'
  rfl

/-- The canonical state layer may be replaced by any layering reconstructing that state. -/
theorem stateSlotFn_eq {w d : ℕ} {ι : Type*} (A : FamilyReconstruction w ι)
    (layer : GNode (A.data.forest A.plain) → ℕ) (hL : IsLayering (A.data.garden A.plain) layer)
    (hspec : layeredReconstruction A.data A.plain layer hL = A.layered)
    (f : ℕ → Fin w → Fin w → Mom d → ℝ) (L γ δ : ℝ) :
    stateSlotFn A f L γ δ = slotFn A.data A.plain L γ δ (typeProfiles A.layered f) layer hL := by
  have hl : layer = stateLayer A :=
    layeredReconstruction_inj A.data A.plain (hspec.trans (stateLayer_spec A).symm)
  subst layer
  rfl

section MemberKernelsMk
variable {w p d : ℕ} {kind : Bool} {S : Garden w}
  (hM : S.molecule.IsMolecule) (σ : Prescription S) {Mk : Set (CLVine S)}
  (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  {Y : FamilyReconstruction w (UnitsIndex (alignedAssemblyMk hM σ Mk))}
  {vs : ∀ j, UnitAt Y.skeleton Y.family ((unitsSplit (alignedAssemblyMk hM σ Mk)).Q j)}
  {xs : List (UnitsIndex (alignedAssemblyMk hM σ Mk))}
  (hr : ReachU p kind (unitsSplit (alignedAssemblyMk hM σ Mk)).Q xs
    (unitsStart (alignedAssemblyMk hM σ Mk) (unitBlkMk_disj hM σ Mk) D hS layer hLayer)
    (unitsRegion (alignedAssemblyMk hM σ Mk) (unitBlkMk_disj hM σ Mk)) Y vs)
  (hn : xs.Nodup)
  {Mk' : Set (CLVine Y.skeleton)} (hT : Stage1Mk.MarkTransported (batchMolIso hr.batch) Mk Mk')

/-- B1b-3 (Mk-general form of `endpointShape_iota`).
Unit reindexing leaves the endpoint's actual slot embedding unchanged. -/
theorem endpointShape_iotaMk
    (hG : (stSt Y.skeleton (transportPrescription (batchMolIso hr.batch) σ) Mk').G.IsPlain) :
    (endpointShapeMk hM σ D hS layer hLayer hr hn hT).iota Y.plain hG =
    (stShape (Mole.garden_isMolecule Y.skeleton) (transportPrescription (batchMolIso hr.batch) σ) Mk').iota Y.plain hG := by
  unfold endpointShapeMk
  rw [congrBlocks_iota]
  rfl

/-- B1b-3 (Mk-general form of `commonShape_slotFn`).
Native outer kernels of every carried member agree on the literal common garden. -/
theorem commonShape_slotFnMk (hG : (stSt S σ Mk).G.IsPlain)
    (f : ℕ → Fin w → Fin w → Mom d → ℝ) (L γ δ : ℝ) (s : ReplacementSlot (stSt S σ Mk).G) :
    slotFn Y.data Y.plain L γ δ (typeProfiles Y.layered f) (stateLayer Y) (stateLayer_isLayering Y)
      ((commonShapeMk hM σ D hS layer hLayer hr hn hT).iota Y.plain hG s) =
    slotFn D hS L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) f) layer hLayer
      ((stShape hM σ Mk).iota hS hG s) := by
  let A := unitsStart (alignedAssemblyMk hM σ Mk) (unitBlkMk_disj hM σ Mk) D hS layer hLayer
  let h := batchMolIso_spec hr.batch
  change stateSlotFn Y f L γ δ _ = _
  unfold commonShapeMk
  erw [cast_iota _ _ Y.plain ((stSt _ _ Mk').plain Y.plain), endpointShape_iotaMk]
  change spliceKernelMk Y (transportPrescription (batchMolIso hr.batch) σ) Mk' f L γ δ _ = _
  erw [batch_spliceKernelMk h σ hT (unitsFamily_isV0FamMk hM σ)]
  unfold spliceKernelMk
  erw [stateSlotFn_eq A layer hLayer rfl]
  rfl

end MemberKernelsMk

variable {w p d : ℕ} {kind : Bool} {S : Garden w}
  (hM : S.molecule.IsMolecule) (σ : Prescription S)
  (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  {Y : FamilyReconstruction w (UnitsIndex (alignedAssembly hM σ))}
  {vs : ∀ j, UnitAt Y.skeleton Y.family ((unitsSplit (alignedAssembly hM σ)).Q j)}
  {xs : List (UnitsIndex (alignedAssembly hM σ))}
  (hr : ReachU p kind (unitsSplit (alignedAssembly hM σ)).Q xs
    (unitsStart (alignedAssembly hM σ) (unitBlk_disj hM σ) D hS layer hLayer)
    (unitsRegion (alignedAssembly hM σ) (unitBlk_disj hM σ)) Y vs)
  (hn : xs.Nodup)

end WaveTurbulence.VineAlign
