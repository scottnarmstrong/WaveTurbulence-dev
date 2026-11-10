/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineBatchOrderedNormalization` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceDiagrams
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCollectionTransport
public import WaveTurbulence.Foundations.Vine.A.VineBatchOrderedNormalization
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
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
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineBatchSplice
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineChainNoCN
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCoarseGardenPartition
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCoarseGroupCode
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineContributingGroups
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineDartAddress
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamilyUnique
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineBatch
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineOperation
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineRebase
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineRecovery
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineRefinement
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupExtension
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkFn
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineOperationSplice
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescribedPartition
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescribedPoints
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceOrdered
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceOuter
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSurvivingDarts
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineWholeUnit
/-! Literal ordered normalization along every actual selected LF batch. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open Stage1 RedSplice LFTwist WaveTurbulence.GammaLow.FinalCount
variable {w p : ℕ} {kind : Bool} {ι : Type*} {L : List ι} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- B1b-2 (Mk-general form of `operation_splice_garden_eq`). -/
theorem operation_splice_garden_eqMk {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} {Mk : Set (CLVineG γ A.skeleton)} (hA : IsV0Fam γ A.family σ Mk)
    (op : FamilyOperation (p := p) (kind := kind) A i)
    {Mk' : Set (CLVineG γ op.output.skeleton)} (hT : Stage1Mk.MarkTransported γ (operationMolIso op) Mk Mk') :
    (stSt γ op.output.skeleton (transportPrescription (operationMolIso op) σ) Mk').G = (stSt γ A.skeleton σ Mk).G := by
  cases op with
  | mk hc he ht hq ε C =>
    cases ε
    · obtain rfl : Mk = Mk' := Stage1Mk.markTransported_refl_eq hT
      exact congrArg (fun τ => (stSt γ A.skeleton τ Mk).G) (transportPrescription_refl σ)
    · exact unitSplice_garden_eqMk (selectedMemberSite γ hA i) σ hT ⟨familyVine γ A.family i, hA.1 i, rfl⟩


/-- B1b-2 (Mk-general form of `BatchIso.splice_garden_eq`). -/
theorem BatchIso.splice_garden_eqMk {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule}
    (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton) {Mk : Set (CLVineG γ A.skeleton)}
    {Mk' : Set (CLVineG γ B.skeleton)}
    (hT : Stage1Mk.MarkTransported γ F Mk Mk') (hA : IsV0Fam γ A.family σ Mk) :
    (stSt γ B.skeleton (transportPrescription F σ) Mk').G = (stSt γ A.skeleton σ Mk).G := by
  induction h with
  | nil =>
    obtain rfl := Stage1Mk.markTransported_refl_eq hT
    exact congrArg (fun τ => (stSt γ _ τ Mk).G) (transportPrescription_refl σ)
  | skip _ _ ih => exact ih σ hT hA
  | @apply L A B i op J h ih =>
    obtain ⟨h1, h2⟩ := Stage1Mk.markTransported_split (operationMolIso op) J hT
    have hb := ih _ h2 (isV0Fam_operationMk hA op h1)
    rw [transportPrescription_trans] at hb
    exact hb.trans (operation_splice_garden_eqMk hA op h1)

/-- Every actual fine batch has exactly the same ordered spliced garden. -/
theorem BatchIso.splice_garden_eq {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule}
    (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton) (hA : IsV0Fam γ A.family σ) :
    (stSt γ B.skeleton (transportPrescription F σ)).G = (stSt γ A.skeleton σ).G :=
  BatchIso.splice_garden_eqMk h σ (Stage1Mk.markTransported_empty F) hA

/-- B1b-2 (Mk-general form of `operation_splice_pi_address`). -/
theorem operation_splice_pi_addressMk {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} {Mk : Set (CLVineG γ A.skeleton)} (hA : IsV0Fam γ A.family σ Mk)
    (op : FamilyOperation (p := p) (kind := kind) A i)
    {Mk' : Set (CLVineG γ op.output.skeleton)} (hT : Stage1Mk.MarkTransported γ (operationMolIso op) Mk Mk')
    (v : GBranch A.skeleton.tree) :
    ((stSt γ op.output.skeleton (transportPrescription (operationMolIso op) σ) Mk').M.pi
      (stSt γ op.output.skeleton (transportPrescription (operationMolIso op) σ) Mk').hcls ((operationMolIso op).e v)).1 =
      ((stSt γ A.skeleton σ Mk).M.pi (stSt γ A.skeleton σ Mk).hcls v).1 := by
  cases op with
  | mk hc he ht hq ε C =>
    cases ε
    · obtain rfl : Mk = Mk' := Stage1Mk.markTransported_refl_eq hT
      exact congrArg (fun τ => ((stSt γ A.skeleton τ Mk).M.pi (stSt γ A.skeleton τ Mk).hcls v).1)
        (transportPrescription_refl σ)
    · let Z := selectedMemberSite γ hA i
      have hs : ∃ c ∈ vinesV0 γ A.skeleton σ Mk, c.atoms = Z.S0 := ⟨familyVine γ A.family i, hA.1 i, rfl⟩
      exact (congrArg Subtype.val (unitSplice_piMk Z σ hT hs v)).trans (unitSpliceMolIso_addressMk Z σ hT hs _)


/-- B1b-2 (Mk-general form of `BatchIso.splice_pi_address`). -/
theorem BatchIso.splice_pi_addressMk {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule}
    (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton) {Mk : Set (CLVineG γ A.skeleton)}
    {Mk' : Set (CLVineG γ B.skeleton)}
    (hT : Stage1Mk.MarkTransported γ F Mk Mk') (hA : IsV0Fam γ A.family σ Mk)
    (v : GBranch A.skeleton.tree) :
    ((stSt γ B.skeleton (transportPrescription F σ) Mk').M.pi
      (stSt γ B.skeleton (transportPrescription F σ) Mk').hcls (F.e v)).1 =
      ((stSt γ A.skeleton σ Mk).M.pi (stSt γ A.skeleton σ Mk).hcls v).1 := by
  induction h with
  | nil =>
    obtain rfl := Stage1Mk.markTransported_refl_eq hT
    change ((stSt γ _ (transportPrescription (molIsoRefl _) σ) Mk).M.pi _ v).1 = _
    rw [transportPrescription_refl]
  | skip _ _ ih => exact ih σ hT hA v
  | @apply L A B i op J h ih =>
    obtain ⟨h1, h2⟩ := Stage1Mk.markTransported_split (operationMolIso op) J hT
    have hb := ih _ h2 (isV0Fam_operationMk hA op h1) ((operationMolIso op).e v)
    rw [transportPrescription_trans] at hb
    exact hb.trans (operation_splice_pi_addressMk hA op h1 v)



/-- B1b-2 (Mk-general form of `BatchIso.spliceMolIso_address`). -/
theorem BatchIso.spliceMolIso_addressMk {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule}
    (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton) {Mk : Set (CLVineG γ A.skeleton)}
    {Mk' : Set (CLVineG γ B.skeleton)}
    (hT : Stage1Mk.MarkTransported γ F Mk Mk') (hA : IsV0Fam γ A.family σ Mk)
    (b : GBranch (stSt γ A.skeleton σ Mk).G.tree) : ((BatchIso.spliceMolIsoMk γ h σ hT hA).e b).1 = b.1 := by
  have hp := BatchIso.splice_piMk h σ hT hA ((stSt γ A.skeleton σ Mk).M.ob b)
  rw [splice_pi_ob] at hp
  exact (congrArg Subtype.val hp).trans
    ((BatchIso.splice_pi_addressMk h σ hT hA _).trans (congrArg Subtype.val (splice_pi_ob _ b)))


/-- B1b-2 (Mk-general form of `BatchIso.splice_branch_cast`). -/
theorem BatchIso.splice_branch_castMk {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule}
    (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton) {Mk : Set (CLVineG γ A.skeleton)}
    {Mk' : Set (CLVineG γ B.skeleton)}
    (hT : Stage1Mk.MarkTransported γ F Mk Mk') (hA : IsV0Fam γ A.family σ Mk)
    (b : GBranch (stSt γ A.skeleton σ Mk).G.tree) :
    gardenBranchCast (BatchIso.splice_garden_eqMk h σ hT hA) ((BatchIso.spliceMolIsoMk γ h σ hT hA).e b) = b :=
  Subtype.ext ((gardenBranchCast_val _ _).trans (BatchIso.spliceMolIso_addressMk h σ hT hA b))


end WaveTurbulence.GammaLow.Fama.VineA
