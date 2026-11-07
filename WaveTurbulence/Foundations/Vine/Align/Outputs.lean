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

/-- Reindexing the unit family recovers the canonical fine state, including replacement data. -/
theorem unitsStart_reindex (hM : S.molecule.IsMolecule) (σ : Prescription S)
    (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (hp : IsPrimeGarden S) :
    ∃ e : UnitsIndex (alignedAssembly hM σ) ≃ CoreIndex (vinesV0 S σ),
      stateReindex ((⟨S, hp, D, D.garden_decodes hS⟩ :
        PrimeData (layeredReconstruction D hS layer hLayer)).fineState σ) e =
        unitsStart (alignedAssembly hM σ) (unitBlk_disj hM σ) D hS layer hLayer :=
  fineState_recovery (unitsStart (alignedAssembly hM σ) (unitBlk_disj hM σ) D hS layer hLayer)
    hp σ (unitsFamily_isV0Fam hM σ)

/-- The unit class and the canonical fine class have exactly the same layered gardens. -/
theorem unitsStart_outputs (hM : S.molecule.IsMolecule) (σ : Prescription S)
    (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (hp : IsPrimeGarden S) :
    (unitsStart (alignedAssembly hM σ) (unitBlk_disj hM σ) D hS layer hLayer).allCoreOutputs
      (p := p) (kind := kind) =
    ((⟨S, hp, D, D.garden_decodes hS⟩ :
      PrimeData (layeredReconstruction D hS layer hLayer)).fineState σ).allCoreOutputs
      (p := p) (kind := kind) := by
  obtain ⟨e, he⟩ := unitsStart_reindex hM σ D hS layer hLayer hp
  rw [← he]
  exact allCoreOutputs_reindex _ e

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

/-- The `hT` premise of `sum_tauClass_vineD_api_dep`, with no extra family-alignment premise. -/
theorem classSum_hT (a : PrescribedPrimeGarden w)
    (T : Finset (LayeredGarden w)) (hT : (T : Set (LayeredGarden w)) = a.outputs (p := p) (kind := kind))
    (layer : GNode (a.prime.data.forest a.prime.prime.1) → ℕ)
    (hLayer : IsLayering (a.prime.data.garden a.prime.prime.1) layer)
    (he : layeredReconstruction a.prime.data a.prime.prime.1 layer hLayer = a.layered) :
    (T : Set (LayeredGarden w)) =
      (unitsStart (alignedAssembly (Mole.garden_isMolecule _) a.totalSigma)
        (unitBlk_disj (Mole.garden_isMolecule _) a.totalSigma)
        a.prime.data a.prime.prime.1 layer hLayer).allCoreOutputs (p := p) (kind := kind) :=
  hT.trans (prescribed_outputs_eq_unitsStart a layer hLayer he)

end WaveTurbulence.VineAlign
