/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineBatchSplice` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.RepPr2Supp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineCoarseGroupCodeSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineFineBatchSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineFineFamilySupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineFineOperationSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineFineRebaseSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineFineRecoverySupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineFineRefinementSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineNormalizedRepSelSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VinePrescribedPointsSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VinePrescriptionSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VinePrimeStateSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineUnitCoverSupp
public import WaveTurbulence.Foundations.Vine.A.VinePieceIndex
public import WaveTurbulence.Foundations.Vine.A.VineBatchSplice
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Amend7
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Deg
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Desig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Final
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Gap
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Greg
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Group
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVC
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.IP
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj3
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Pairs
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Rev
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Runs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK3
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Skip
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.SurvData
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.SurvMK
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceSurvMK2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Top
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.TripleDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.TripleHinge
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.VC
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Famb.Molecule.TwistSourceFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineChainNoCN
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamilyUnique
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineBatch
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineOperation
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineOperationSplice
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineReindex
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunChain
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunSelected
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineSkipSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitClasses
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitCover
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitCoverOne
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitDeletedDarts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitImageCover
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitList
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitMergedLeaves
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelectedMK
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceBranch
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceChildren
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceDarts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceLeafParents
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceLeaves
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceNodes
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSurvivingDarts
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineWholeUnit
/-! Actual simultaneous-splice quotient maps along selected LF batches. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open Stage1 RedSplice LFTwist WaveTurbulence.GammaLow.FinalCount
variable {w p : ℕ} {kind : Bool} {ι : Type*} {L : List ι} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]
variable {A B : FamilyReconstruction w ι} {F : MolIso A.skeleton.molecule B.skeleton.molecule}

/-- B1b-2 (Mk-general form of `BatchIso.splice_classes`). -/
theorem BatchIso.splice_classesMk (h : BatchIso p kind L A B F)
    (σ : Prescription A.skeleton) {Mk : Set (CLVineG γ A.skeleton)} {Mk' : Set (CLVineG γ B.skeleton)}
    (hT : Stage1Mk.MarkTransported γ F Mk Mk') (hA : IsV0Fam γ A.family σ Mk) (b : GBranch A.skeleton.tree) :
    (stSt γ B.skeleton (transportPrescription F σ) Mk').cls (F.e b) =
      ((stSt γ A.skeleton σ Mk).cls b).map F.e := by
  induction h with
  | nil A =>
    obtain rfl := Stage1Mk.markTransported_refl_eq hT
    rw [transportPrescription_refl]
    change (stSt γ A.skeleton σ Mk).cls b = ((stSt γ A.skeleton σ Mk).cls b).map id
    cases (stSt γ A.skeleton σ Mk).cls b <;> rfl
  | skip _ _ ih => exact ih σ hT hA b
  | @apply L A B i op J h ih =>
    obtain ⟨h1, h2⟩ := Stage1Mk.markTransported_split (operationMolIso op) J hT
    have hh := ih (transportPrescription (operationMolIso op) σ) h2
      (isV0Fam_operationMk hA op h1) ((operationMolIso op).e b)
    rw [transportPrescription_trans, operation_splice_classesMk hA op h1 b] at hh
    simpa only [Option.map_map, molIsoTrans, Equiv.coe_trans, Function.comp_def] using hh


/-- B1b-2 (Mk-general form of `BatchIso.spliceMolIso`). -/
noncomputable def BatchIso.spliceMolIsoMk (γ : ℝ) [Fact (γ ≤ 1 / 2)] (h : BatchIso p kind L A B F)
    (σ : Prescription A.skeleton) {Mk : Set (CLVineG γ A.skeleton)} {Mk' : Set (CLVineG γ B.skeleton)}
    (hT : Stage1Mk.MarkTransported γ F Mk Mk') (hA : IsV0Fam γ A.family σ Mk) :
    MolIso (stSt γ A.skeleton σ Mk).G.molecule
      (stSt γ B.skeleton (transportPrescription F σ) Mk').G.molecule :=
  quotientMolIso F (BatchIso.splice_classesMk h σ hT hA) (stSt γ A.skeleton σ Mk).M
    (stSt γ B.skeleton (transportPrescription F σ) Mk').M


/-- B1b-2 (Mk-general form of `BatchIso.spliceMolIso_branch_names`). -/
theorem BatchIso.spliceMolIso_branch_namesMk (h : BatchIso p kind L A B F)
    (σ : Prescription A.skeleton) {Mk : Set (CLVineG γ A.skeleton)} {Mk' : Set (CLVineG γ B.skeleton)}
    (hT : Stage1Mk.MarkTransported γ F Mk Mk') (hA : IsV0Fam γ A.family σ Mk)
    (c : GBranch (stSt γ A.skeleton σ Mk).G.tree) :
    (stSt γ B.skeleton (transportPrescription F σ) Mk').M.ob ((BatchIso.spliceMolIsoMk γ h σ hT hA).e c) =
      F.e ((stSt γ A.skeleton σ Mk).M.ob c) :=
  quotientBranchEquiv_comm F (BatchIso.splice_classesMk h σ hT hA) _ _ c




/-- B1b-3: the splice state's hinge set (branches with a splice class, `SpState.hinges`) follows the actual batch
map at markings carried by the batch. It reads neither hinge pairs nor the gap specification. -/
theorem BatchIso.splice_hinge_iffMk (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    {Mk : Set (CLVineG γ A.skeleton)} {Mk' : Set (CLVineG γ B.skeleton)}
    (hT : Stage1Mk.MarkTransported γ F Mk Mk') (hA : IsV0Fam γ A.family σ Mk)
    (c : GBranch (stSt γ A.skeleton σ Mk).G.tree) :
    (BatchIso.spliceMolIsoMk γ h σ hT hA).e c ∈ (stSt γ B.skeleton (transportPrescription F σ) Mk').hinges ↔
      c ∈ (stSt γ A.skeleton σ Mk).hinges := by
  let S := stSt γ A.skeleton σ Mk
  let T := stSt γ B.skeleton (transportPrescription F σ) Mk'
  have he : T.cls (T.M.ob ((BatchIso.spliceMolIsoMk γ h σ hT hA).e c)) = (S.cls (S.M.ob c)).map F.e :=
    (congrArg T.cls (BatchIso.spliceMolIso_branch_namesMk h σ hT hA c)).trans (BatchIso.splice_classesMk h σ hT hA (S.M.ob c))
  have hn : ((S.cls (S.M.ob c)).map F.e ≠ none) ↔ S.cls (S.M.ob c) ≠ none := by
    cases S.cls (S.M.ob c) <;> simp
  exact (T.mem_hinges _).trans
    ((Iff.of_eq (congrArg (fun o : Option (GBranch B.skeleton.tree) => o ≠ none) he)).trans
      (hn.trans (S.mem_hinges c).symm))

/-- B1b-3: the complete splice hinge sets correspond by the actual batch quotient map. -/
theorem BatchIso.splice_hinges_imageMk (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    {Mk : Set (CLVineG γ A.skeleton)} {Mk' : Set (CLVineG γ B.skeleton)}
    (hT : Stage1Mk.MarkTransported γ F Mk Mk') (hA : IsV0Fam γ A.family σ Mk) :
    (stSt γ A.skeleton σ Mk).hinges.image (BatchIso.spliceMolIsoMk γ h σ hT hA).e =
      (stSt γ B.skeleton (transportPrescription F σ) Mk').hinges := by
  ext y
  obtain ⟨x, rfl⟩ := (BatchIso.spliceMolIsoMk γ h σ hT hA).e.surjective y
  constructor
  · intro hy
    obtain ⟨c, hc, he⟩ := Finset.mem_image.mp hy
    exact (BatchIso.splice_hinge_iffMk h σ hT hA x).mpr ((BatchIso.spliceMolIsoMk γ h σ hT hA).e.injective he ▸ hc)
  · intro hy
    exact Finset.mem_image.mpr ⟨x, (BatchIso.splice_hinge_iffMk h σ hT hA x).mp hy, rfl⟩

end WaveTurbulence.GammaLow.Fama.VineA
