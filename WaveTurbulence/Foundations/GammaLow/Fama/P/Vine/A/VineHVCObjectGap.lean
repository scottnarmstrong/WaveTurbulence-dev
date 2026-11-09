/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineHVCObjectGap` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineGroupCandidateMapSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineNormalizationNamesSupp
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineHyperGapChoice
public import WaveTurbulence.Foundations.Vine.A.VineHVCObjectGap
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceFlowKind
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainFlows
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineBatchSplice
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineChainNoCN
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCoarseGardenPartition
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCollectionTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineContributingGroups
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineDesignatedSupport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamilyUnique
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineBatch
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineOperation
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineRebase
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineRecovery
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineRefinement
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGapJointChoice
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupExtension
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineHyperDesignation
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkFn
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineObjectGeometry
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitSurvivingDarts
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineWholeUnit
/-! HVC supports have an intrinsic designated bond up to mates, so the actual
hyper-object gap kind is independent of both designation and joint choices. -/
@[expose] public section
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open Finset Stage1 LGSpine.SourceVine WaveTurbulence.GammaLow.FinalCount
variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {d : ℕ} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- Two arbitrary hyper presentations on an HVC support use the same actual bond. -/
theorem hyper_designations_unique_of_HVC (hM : M.IsMolecule) {S : Finset V} {a b c e f g : V}
    (hHVC : Src.IsHVC γ M S a b) (P : Src.HyperLikeRealization γ M S c e) (Q : Src.HyperLikeRealization γ M S f g) :
    P.added = Q.added ∨ P.added = M.mate Q.added := by
  obtain ⟨r, hr, hR, n, hn, hc⟩ := hHVC
  have hP := hyper_added_unique_of_chain hM r P.added hr P.ends_eq hR P.adjoint.1 hn hc
  have hQ := hyper_added_unique_of_chain hM r Q.added hr Q.ends_eq hR Q.adjoint.1 hn hc
  rcases hP with hp | hp <;> rcases hQ with hq | hq
  · exact Or.inl (hp.symm.trans hq)
  · exact Or.inr (hp.symm.trans hq)
  · right
    have he := congrArg M.mate (hp.symm.trans hq)
    rwa [M.mate_mate] at he
  · left
    have he := congrArg M.mate (hp.symm.trans hq)
    simpa only [M.mate_mate] using he

/-- No independent choice of a designated object changes the gap-kind predicate on an HVC support. -/
theorem objects_gapKind_iff_of_HVC (hM : M.IsMolecule) (P Q : Src.Object γ M) (hat : P.atoms = Q.atoms)
    {a b : V} (hHVC : Src.IsHVC γ M P.atoms a b)
    (scale γ' η : ℝ) (base : Mom d) (charge : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration scale base charge κ) (hc0 : ∀ v ∈ M.atoms, M.deg v = 4 → charge v = 0)
    (kind : Molecule.GapKind) : P.HasGapKind scale γ' η base κ kind ↔ Q.HasGapKind scale γ' η base κ kind := by
  rcases P with ⟨S, u, v, ps⟩
  rcases Q with ⟨T, x, y, qs⟩
  change S = T at hat
  subst T
  have hex : ∃ e : D, M.ends e = s(a, b) ∧ (Mole.eraseBond M e).IsBlock S a b := by
    obtain ⟨e, he, hb, _⟩ := hHVC
    exact ⟨e, he, hb⟩
  cases ps with
  | vc hP =>
    obtain ⟨e, he, hb⟩ := hex
    exact (block_not_hyper hP.1 e he hb).elim
  | hyper R =>
    cases qs with
    | vc hQ =>
      obtain ⟨e, he, hb⟩ := hex
      exact (block_not_hyper hQ.1 e he hb).elim
    | hyper U =>
      exact hyper_gapKind_iff_of_same_bond hM R U (hyper_designations_unique_of_HVC hM hHVC R U)
        scale γ' η base charge κ hκ hc0 kind

end WaveTurbulence.GammaLow.Fama.VineA
