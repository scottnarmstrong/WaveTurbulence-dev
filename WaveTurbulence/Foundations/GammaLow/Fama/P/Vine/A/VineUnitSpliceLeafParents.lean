/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineUnitSpliceLeafParents` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceLeaves
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceLeafParents
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitMergedLeaves
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelectedMK
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceBranch
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSpliceIso
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineWholeUnit
/-! The full surviving-leaf correspondence preserves actual roots, all
parent incidences and tree indices across selected simultaneous LF splices. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.GammaLow.FinalCount
variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]


/-- B1b-2 (Mk-general form of `unitSpliceLeafEquiv_root_address`). -/
theorem unitSpliceLeafEquiv_root_addressMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0) (q : GLeaf (stSt γ G σ Mk).G.tree)
    (hq : q.1.2 = []) : (unitSpliceLeafEquivMk γ Z σ hT hsel q).1 = q.1 := by
  have hnew := (unitSpliceLeafEquiv_rootMk Z σ hT hsel q).mpr hq
  have ho := ((spliceFoldLeafTrace (unitBlocks γ G σ Mk)).root q).mpr hq
  exact ((spliceFoldLeafTrace (unitBlocks γ Z.target (transportPrescription Z.iso σ) Mk')).root_address _ hnew).symm.trans
    ((congrArg Subtype.val (unitSpliceLeafEquiv_namesMk Z σ hT hsel q)).trans
      ((coreLeaf_root_address Z.P _ ho).trans ((spliceFoldLeafTrace (unitBlocks γ G σ Mk)).root_address q hq)))


/-- B1b-2 (Mk-general form of `unitSpliceLeafEquiv_parent`). -/
theorem unitSpliceLeafEquiv_parentMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0) (q : GLeaf (stSt γ G σ Mk).G.tree) (hn : q.1.2 ≠ []) :
    let e := unitSpliceLeafEquivMk γ Z σ hT hsel
    let hnew : (e q).1.2 ≠ [] := fun h => hn ((unitSpliceLeafEquiv_rootMk Z σ hT hsel q).mp h)
    (unitSpliceMolIsoMk γ Z σ hT hsel).e (GNode.parent q.toNode hn) = GNode.parent (e q).toNode hnew := by
  dsimp only
  let e := unitSpliceLeafEquivMk γ Z σ hT hsel
  let T := spliceFoldLeafTrace (unitBlocks γ G σ Mk)
  let U := spliceFoldLeafTrace (unitBlocks γ Z.target (transportPrescription Z.iso σ) Mk')
  let M := (stSt γ G σ Mk).M
  let N := (stSt γ Z.target (transportPrescription Z.iso σ) Mk').M
  have hnew : (e q).1.2 ≠ [] := fun h => hn ((unitSpliceLeafEquiv_rootMk Z σ hT hsel q).mp h)
  have ho : (T.leaf q).1.2 ≠ [] := fun h => hn ((T.root q).mp h)
  have hon : (U.leaf (e q)).1.2 ≠ [] := fun h => hnew ((U.root (e q)).mp h)
  have hne : T.leaf q ≠ G.pair Z.P.retained := fun he => active_pair_not_survivingMk Z σ hsel ⟨q, he⟩
  have hpn : GNode.parent (U.leaf (e q)).toNode hon =
      GNode.parent (coreLeafEquiv G Z.P (T.leaf q)).toNode ((coreLeafEquiv_nonroot G Z.P _).mpr ho) := by
    apply Subtype.ext
    change ((U.leaf (e q)).1.1, (U.leaf (e q)).1.2.dropLast) =
      ((coreLeafEquiv G Z.P (T.leaf q)).1.1, (coreLeafEquiv G Z.P (T.leaf q)).1.2.dropLast)
    exact congrArg (fun l : GLeaf Z.target.tree => (l.1.1, l.1.2.dropLast))
      (unitSpliceLeafEquiv_namesMk Z σ hT hsel q)
  have hp : GNode.parent (U.leaf (e q)).toNode hon = Z.iso.e (GNode.parent (T.leaf q).toNode ho) :=
    hpn.trans (leafParent_transport G Z.P (T.leaf q) ho hne)
  apply N.ob_inj
  exact (unitSpliceMolIso_branch_namesMk Z σ hT hsel (GNode.parent q.toNode hn)).trans
    ((congrArg Z.iso.e (T.parent q hn ho)).trans
      ((unitBlocks_repC_twistMk Z σ hT hsel (GNode.parent (T.leaf q).toNode ho)).symm.trans
        ((congrArg (repC (stSt γ Z.target (transportPrescription Z.iso σ) Mk').cls) hp).symm.trans
          (U.parent (e q) hnew hon).symm)))


/-- B1b-2 (Mk-general form of `unitSpliceLeafEquiv_index`). -/
theorem unitSpliceLeafEquiv_indexMk (Z : TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 γ G σ Mk, c.atoms = Z.S0) (q : GLeaf (stSt γ G σ Mk).G.tree) :
    (unitSpliceLeafEquivMk γ Z σ hT hsel q).1.1 = q.1.1 := by
  by_cases hroot : q.1.2 = []
  · exact congrArg Prod.fst (unitSpliceLeafEquiv_root_addressMk Z σ hT hsel q hroot)
  · have hp := unitSpliceLeafEquiv_parentMk Z σ hT hsel q hroot
    have hi := unitSpliceMolIso_branch_indexMk Z σ hT hsel (GNode.parent q.toNode hroot)
    have he := congrArg (fun b : GBranch (stSt γ Z.target (transportPrescription Z.iso σ) Mk').G.tree => b.1.1) hp
    exact he.symm.trans hi


end WaveTurbulence.GammaLow.Fama.VineA
