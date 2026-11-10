/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.Align.Units
public import WaveTurbulence.Foundations.Vine.A.VineGardenOrbits
public import WaveTurbulence.Foundations.Stage1.Represents.RepPr1
/-! Equality of the two actual once-per-member output sets. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineAlign
open VineEstS2 VineEstS4 VineA VineB VineC RedSplice Stage1 Twist RegRed Represents LFTwist Reg.Skeleton
variable {w p : ℕ} {kind : Bool} {S : Garden w}

/-- B1b (Mk-general form of `unitsStart_reindex`). -/
theorem unitsStart_reindexMk (hM : S.molecule.IsMolecule) (σ : Prescription S)
    (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (hp : IsPrimeGarden S) {Mk : Set (Stage1.CLVine _)} :
    ∃ e : UnitsIndex (alignedAssemblyMk (Mk := Mk) hM σ) ≃ CoreIndex (vinesV0 (Mk := Mk) S σ),
      stateReindex ((⟨S, hp, D, D.garden_decodes hS⟩ :
        PrimeData (layeredReconstruction D hS layer hLayer)).fineState (Mk := Mk) σ) e =
        unitsStart (alignedAssemblyMk (Mk := Mk) hM σ) (unitBlkMk_disj (Mk := Mk) hM σ) D hS layer hLayer :=
  fineState_recoveryMk (Mk := Mk) (unitsStart (alignedAssemblyMk (Mk := Mk) hM σ) (unitBlkMk_disj (Mk := Mk) hM σ) D hS layer hLayer)
    hp σ (unitsFamily_isV0FamMk (Mk := Mk) hM σ)

/-- B1b (Mk-general form of `unitsStart_outputs`). -/
theorem unitsStart_outputsMk (hM : S.molecule.IsMolecule) (σ : Prescription S)
    (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (hp : IsPrimeGarden S) {Mk : Set (Stage1.CLVine _)} :
    (unitsStart (alignedAssemblyMk (Mk := Mk) hM σ) (unitBlkMk_disj (Mk := Mk) hM σ) D hS layer hLayer).allCoreOutputs
      (p := p) (kind := kind) =
    ((⟨S, hp, D, D.garden_decodes hS⟩ :
      PrimeData (layeredReconstruction D hS layer hLayer)).fineState (Mk := Mk) σ).allCoreOutputs
      (p := p) (kind := kind) := by
  obtain ⟨e, he⟩ := unitsStart_reindexMk (Mk := Mk) hM σ D hS layer hLayer hp
  rw [← he]
  exact allCoreOutputs_reindex _ e

/-- The unit class and the canonical fine class have exactly the same layered gardens. -/
theorem unitsStart_outputs (hM : S.molecule.IsMolecule) (σ : Prescription S)
    (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (hp : IsPrimeGarden S) :
    (unitsStart (alignedAssembly hM σ) (unitBlk_disj hM σ) D hS layer hLayer).allCoreOutputs
      (p := p) (kind := kind) =
    ((⟨S, hp, D, D.garden_decodes hS⟩ :
      PrimeData (layeredReconstruction D hS layer hLayer)).fineState σ).allCoreOutputs
      (p := p) (kind := kind) := unitsStart_outputsMk (Mk := ∅) hM σ D hS layer hLayer hp

/-- B1b-2 (Mk-general form of `prescribed_outputs_eq_unitsStart`): the fine′ output set of a prescribed point at the
marking `mk` is the class of the run assembly (units = runs at marked groups). -/
theorem prescribed_outputs_eq_unitsStartMk (a : PrescribedPrimeGarden w) (mk : Stage1Mk.MarkFn w)
    (layer : GNode (a.prime.data.forest a.prime.prime.1) → ℕ)
    (hLayer : IsLayering (a.prime.data.garden a.prime.prime.1) layer)
    (he : layeredReconstruction a.prime.data a.prime.prime.1 layer hLayer = a.layered) :
    a.outputs (p := p) (kind := kind) mk =
      (unitsStart (alignedAssemblyMk (Mole.garden_isMolecule _) a.totalSigma (mk a.prime))
        (unitBlkMk_disj (Mole.garden_isMolecule _) a.totalSigma (mk a.prime))
        a.prime.data a.prime.prime.1 layer hLayer).allCoreOutputs (p := p) (kind := kind) := by
  rw [unitsStart_outputsMk _ _ _ _ _ _ a.prime.prime]
  apply congrArg (fun X : FamilyReconstruction w (CoreIndex (vinesV0 a.prime.skeleton a.totalSigma (mk a.prime))) =>
    X.allCoreOutputs (p := p) (kind := kind))
  apply familyReconstruction_ext
  · rfl
  · rfl
  · rfl
  · exact he.symm

/-- B1b-2 (Mk-general form of `classSum_hT`). -/
theorem classSum_hTMk (a : PrescribedPrimeGarden w) (mk : Stage1Mk.MarkFn w)
    (T : Finset (LayeredGarden w)) (hT : (T : Set (LayeredGarden w)) = a.outputs (p := p) (kind := kind) mk)
    (layer : GNode (a.prime.data.forest a.prime.prime.1) → ℕ)
    (hLayer : IsLayering (a.prime.data.garden a.prime.prime.1) layer)
    (he : layeredReconstruction a.prime.data a.prime.prime.1 layer hLayer = a.layered) :
    (T : Set (LayeredGarden w)) =
      (unitsStart (alignedAssemblyMk (Mole.garden_isMolecule _) a.totalSigma (mk a.prime))
        (unitBlkMk_disj (Mole.garden_isMolecule _) a.totalSigma (mk a.prime))
        a.prime.data a.prime.prime.1 layer hLayer).allCoreOutputs (p := p) (kind := kind) :=
  hT.trans (prescribed_outputs_eq_unitsStartMk a mk layer hLayer he)

/-- The producer's prescribed tau class is the unit class used by VINE-C. -/
theorem prescribed_outputs_eq_unitsStart (a : PrescribedPrimeGarden w)
    (layer : GNode (a.prime.data.forest a.prime.prime.1) → ℕ)
    (hLayer : IsLayering (a.prime.data.garden a.prime.prime.1) layer)
    (he : layeredReconstruction a.prime.data a.prime.prime.1 layer hLayer = a.layered) :
    a.outputs (p := p) (kind := kind) =
      (unitsStart (alignedAssembly (Mole.garden_isMolecule _) a.totalSigma)
        (unitBlk_disj (Mole.garden_isMolecule _) a.totalSigma)
        a.prime.data a.prime.prime.1 layer hLayer).allCoreOutputs (p := p) (kind := kind) := by
  rw [unitsStart_outputs _ _ _ _ _ _ a.prime.prime]
  apply congrArg (fun X : FamilyReconstruction w (CoreIndex (vinesV0 a.prime.skeleton a.totalSigma)) =>
    X.allCoreOutputs (p := p) (kind := kind))
  apply familyReconstruction_ext
  · rfl
  · rfl
  · rfl
  · exact he.symm

end WaveTurbulence.VineAlign
