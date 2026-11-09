/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineUnitSpliceLeaves` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitMergedLeaves
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceBranch
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceLeaves
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
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
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelectedMK
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceIso
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineWholeUnit
/-! The full surviving-leaf equivalence for actual simultaneous selected
splices preserves pairing, marks and roots. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.GammaLow.FinalCount
variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- B1b-2 (Mk-general form of `unitSpliceLeafEquiv`). -/
noncomputable def unitSpliceLeafEquivMk (γ : ℝ) [Fact (γ ≤ 1 / 2)] (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0) :
    GLeaf (stSt γ G σ Mk).G.tree ≃ GLeaf (stSt γ Z.target (transportPrescription Z.iso σ) Mk').G.tree :=
  equivOfSameRange (fun q => coreLeafEquiv G Z.P ((spliceFoldLeafTrace (unitBlocks γ G σ Mk)).leaf q))
    (spliceFoldLeafTrace (unitBlocks γ Z.target (transportPrescription Z.iso σ) Mk')).leaf
    ((coreLeafEquiv G Z.P).injective.comp (spliceFoldLeafTrace (unitBlocks γ G σ Mk)).injective)
    (spliceFoldLeafTrace (unitBlocks γ Z.target (transportPrescription Z.iso σ) Mk')).injective
    (unitTwist_splice_leaf_rangesMk Z σ hT hsel)


/-- B1b-2 (Mk-general form of `unitSpliceLeafEquiv_names`). -/
theorem unitSpliceLeafEquiv_namesMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0) (q : GLeaf (stSt γ G σ Mk).G.tree) :
    (spliceFoldLeafTrace (unitBlocks γ Z.target (transportPrescription Z.iso σ) Mk')).leaf (unitSpliceLeafEquivMk γ Z σ hT hsel q) =
      coreLeafEquiv G Z.P ((spliceFoldLeafTrace (unitBlocks γ G σ Mk)).leaf q) :=
  equivOfSameRange_comm _ _ _ _ (unitTwist_splice_leaf_rangesMk Z σ hT hsel) q


/-- B1b-2 (Mk-general form of `unitSpliceLeafEquiv_pair`). -/
theorem unitSpliceLeafEquiv_pairMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0) (q : GLeaf (stSt γ G σ Mk).G.tree) :
    unitSpliceLeafEquivMk γ Z σ hT hsel ((stSt γ G σ Mk).G.pair q) =
      (stSt γ Z.target (transportPrescription Z.iso σ) Mk').G.pair (unitSpliceLeafEquivMk γ Z σ hT hsel q) := by
  apply (spliceFoldLeafTrace (unitBlocks γ Z.target (transportPrescription Z.iso σ) Mk')).injective
  exact (unitSpliceLeafEquiv_namesMk Z σ hT hsel ((stSt γ G σ Mk).G.pair q)).trans
    ((congrArg (coreLeafEquiv G Z.P) ((spliceFoldLeafTrace (unitBlocks γ G σ Mk)).pair q)).trans
      ((unitTwistGarden_pair G Z.P _).symm.trans
        ((congrArg Z.target.pair (unitSpliceLeafEquiv_namesMk Z σ hT hsel q).symm).trans
          ((spliceFoldLeafTrace (unitBlocks γ Z.target (transportPrescription Z.iso σ) Mk')).pair
            (unitSpliceLeafEquivMk γ Z σ hT hsel q)).symm)))


/-- B1b-2 (Mk-general form of `unitSpliceLeafEquiv_mark`). -/
theorem unitSpliceLeafEquiv_markMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0) (q : GLeaf (stSt γ G σ Mk).G.tree) :
    (stSt γ Z.target (transportPrescription Z.iso σ) Mk').G.mark (unitSpliceLeafEquivMk γ Z σ hT hsel q) =
      (stSt γ G σ Mk).G.mark q := by
  exact ((spliceFoldLeafTrace (unitBlocks γ Z.target (transportPrescription Z.iso σ) Mk')).mark _).trans
    ((congrArg Z.target.mark (unitSpliceLeafEquiv_namesMk Z σ hT hsel q)).trans
      ((unitTwistGarden_mark G Z.P _).trans ((spliceFoldLeafTrace (unitBlocks γ G σ Mk)).mark q).symm))


/-- B1b-2 (Mk-general form of `unitSpliceLeafEquiv_root`). -/
theorem unitSpliceLeafEquiv_rootMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0) (q : GLeaf (stSt γ G σ Mk).G.tree) :
    (unitSpliceLeafEquivMk γ Z σ hT hsel q).1.2 = [] ↔ q.1.2 = [] := by
  have ho : (coreLeafEquiv G Z.P ((spliceFoldLeafTrace (unitBlocks γ G σ Mk)).leaf q)).1.2 = [] ↔
      ((spliceFoldLeafTrace (unitBlocks γ G σ Mk)).leaf q).1.2 = [] := by
    simpa only [not_not] using not_congr (coreLeafEquiv_nonroot G Z.P _)
  exact ((spliceFoldLeafTrace (unitBlocks γ Z.target (transportPrescription Z.iso σ) Mk')).root _).symm.trans
    ((Iff.of_eq (congrArg (fun l : GLeaf Z.target.tree => l.1.2 = [])
      (unitSpliceLeafEquiv_namesMk Z σ hT hsel q))).trans
        (ho.trans ((spliceFoldLeafTrace (unitBlocks γ G σ Mk)).root q)))


/-- B1b-2 (Mk-general form of `active_retained_not_surviving`). -/
theorem active_retained_not_survivingMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)}
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0) :
    ¬ ∃ q, (spliceFoldLeafTrace (unitBlocks γ G σ Mk)).leaf q = Z.P.retained := by
  let lp : Mole.GardenLPLeaf G :=
    ⟨Z.P.retained, Z.P.unmarked, retained_nonroot G Z.P, Z.P.paired_nonroot⟩
  have hd : DeletedDart (spliceFold G (unitBlocks γ G σ Mk)).cls (.inr lp) :=
    active_internal_dart_mergedMk Z σ hsel (retainedLP_inGroup Z)
  intro hr
  exact ((spliceFold_leaf_range (unitBlocks γ G σ Mk) Z.P.retained).mp hr) ⟨lp, rfl, hd⟩


/-- B1b-2 (Mk-general form of `active_pair_not_surviving`). -/
theorem active_pair_not_survivingMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)}
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0) :
    ¬ ∃ q, (spliceFoldLeafTrace (unitBlocks γ G σ Mk)).leaf q = G.pair Z.P.retained := by
  rintro ⟨q, he⟩
  apply active_retained_not_survivingMk Z σ hsel
  refine ⟨(stSt γ G σ Mk).G.pair q, ?_⟩
  exact ((spliceFoldLeafTrace (unitBlocks γ G σ Mk)).pair q).trans
    ((congrArg G.pair he).trans (G.pair_pair Z.P.retained))


/-- B1b-2 (Mk-general form of `unitSpliceLeafEquiv_sign`). -/
theorem unitSpliceLeafEquiv_signMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0) (q : GLeaf (stSt γ G σ Mk).G.tree) :
    (stSt γ Z.target (transportPrescription Z.iso σ) Mk').G.sign (unitSpliceLeafEquivMk γ Z σ hT hsel q).toNode =
      (stSt γ G σ Mk).G.sign q.toNode := by
  have hr : (spliceFoldLeafTrace (unitBlocks γ G σ Mk)).leaf q ≠ Z.P.retained :=
    fun he => active_retained_not_survivingMk Z σ hsel ⟨q, he⟩
  have hp : (spliceFoldLeafTrace (unitBlocks γ G σ Mk)).leaf q ≠ G.pair Z.P.retained :=
    fun he => active_pair_not_survivingMk Z σ hsel ⟨q, he⟩
  have hs : Z.target.sign (coreLeafEquiv G Z.P ((spliceFoldLeafTrace (unitBlocks γ G σ Mk)).leaf q)).toNode =
      G.sign ((spliceFoldLeafTrace (unitBlocks γ G σ Mk)).leaf q).toNode := by
    change nodeSign G.sig (coreLeafEquiv G Z.P _).1 = _
    rw [coreLeafEquiv_sign, coreLeafMultiplier, ite_eq_right (not_or_intro hr hp), one_mul]
  exact ((spliceFoldLeafTrace (unitBlocks γ Z.target (transportPrescription Z.iso σ) Mk')).sign _).trans
    ((congrArg (fun l : GLeaf Z.target.tree => Z.target.sign l.toNode)
      (unitSpliceLeafEquiv_namesMk Z σ hT hsel q)).trans
        (hs.trans ((spliceFoldLeafTrace (unitBlocks γ G σ Mk)).sign q).symm))


end WaveTurbulence.GammaLow.Fama.VineA
