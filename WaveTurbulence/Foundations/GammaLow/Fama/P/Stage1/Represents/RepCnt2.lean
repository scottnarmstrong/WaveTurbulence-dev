/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Represents.RepCnt2` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Represents.RepCnt2
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.SubproGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.SubproIso2
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepUG1
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineOperation
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineReindex
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunChain
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunSelected
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineSkipSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitCover
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitCoverOne
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelectedMK
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineWholeUnit
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.B.Fold8
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAffineBoundaryRows
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyAtomSlots
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyAtoms
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyChart
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyChartEquations
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyCoefficients
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyDecode
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyIndex
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyInputEquations
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyPhysicalResonance
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyPieceCoordinates
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyPieceStates
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyPieces
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyResonances
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyRowEquiv
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyShape
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblySlotResonance
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblySourceAnchors
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblySourceStates
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLBoundaryPredecessorApply
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLBoundaryPredecessorCoefficients
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainAssembly
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainCoordinates
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainDifferences
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainInverseRows
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainLocalWitnesses
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainOriginGeometry
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainOrigins
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainPhysicalCoordinates
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChartSourceAffineRows
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChartTagAffineDifferences
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLClockReindex
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLCoordinateChartTagDifferences
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLFrozenAffineDifferences
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLFrozenFormRows
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLGlobalPhase
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLGlobalPhaseExponent
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLInverseMatrixApply
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLInverseMatrixData
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLInverseMatrixIdentities
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLLinearSumintDatum
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLMatrixPredecessorCoefficients
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLMatrixPredecessorIdentity
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLNormalizedCoordinates
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLNormalizedInverseMatrix
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLNormalizedPredecessorSystem
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLRegionalPhaseSlots
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLStep2Momenta
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLStep2Time
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLStep2Weights
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLSumintAlgebraicHypotheses
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLSumintMatrices
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLSumintMatrixValues
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLSumintPredecessors
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLSumintRows
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.ChainChartIndexing
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.ChainPieces
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.ChainPrefixBlocks
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.VineChainSumintForm
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.AssemblyClocked
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.BadClause
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.BadClauseA
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.BadClauseD
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.BadGeom
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.ClockSlots
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.CohmolBound
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.ConstraintsOK
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.EpsLabels
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.IncohDict
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.LayerFacts
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.LeafChild
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.LeafWire
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.NativeRows
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.RowAlign
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.RowAlignRows
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.Step3At
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.Step3DataS1
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.Step3Facts
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.Step3Final
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.TreeClockOrder
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.VineMonotone
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.AssemblyReach
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.AssemblyTwist
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.Class
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.PieceFamily
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.RowCoh
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.RowOrderS1
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.RowReach
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.RowSum
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.AbsBase2
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.Cont.Class
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.Cont.ModClass
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.Cont.ModCore
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.Cont.ModKernel
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelAbs2
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelFlat
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelLoc2
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelRec
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelRecurse
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.NativeRowsH
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.NestGeom
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.ModStatement
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.Step3AtH


/-!
# S2 REPRESENTS, `Stage1Counts` item 3, part 2: the order of `G_sb` and the number of hinges

For the splice `stSt γ S σ` of the (pairwise disjoint) units `unitBlocks γ S σ` of a molecule garden:
`n_sb + |A| = n_sk + #hinges` where `A` is the set of merged atoms (`|A| = Σ_u |u.atoms|`), and `#hinges ≤ #units`.
Consequently `n_sb + #hinges ≤ n_sk` and `n_sb + Σ_u (|u.atoms| - 1) ≤ n_sk`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract WaveTurbulence.GammaLow.FinalCount
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.Represents
open WaveTurbulence.Represents WaveTurbulence.GammaLow.FinalCount
open Finset TTree WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {S : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]



section Counts
variable (hM : S.molecule.IsMolecule) (σ : Prescription S)
include hM

/-- The merged atoms of the splice. -/
noncomputable def mergedAtoms (Mk : Set (CLVineG γ S) := ∅) : Finset (GBranch S.tree) :=
  by classical exact Finset.univ.filter fun v => (stSt γ S σ Mk).cls v ≠ none

/-- The crown atoms of the splice. -/
noncomputable def crownAtoms (Mk : Set (CLVineG γ S) := ∅) : Finset (GBranch S.tree) :=
  by classical exact Finset.univ.filter fun v => (stSt γ S σ Mk).cls v = some v

/-- B1b (Mk-general form of `card_mergedAtoms`). -/
theorem card_mergedAtomsMk {Mk : Set (CLVineG γ _)} : (mergedAtoms (γ := γ) (Mk := Mk) σ).card = ((unitBlocks γ (Mk := Mk) S σ).map fun u => u.atoms.card).sum := by
  classical
  rw [← card_union_blocks _ (unitBlocks_pairwiseMk (Mk := Mk) hM σ)]
  congr 1
  ext v
  simp only [mergedAtoms, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    by_contra hn
    push Not at hn
    exact h (stSt_cls_noneMk (Mk := Mk) hM σ hn)
  · rintro ⟨u, hu, hv⟩
    rw [stSt_cls_memMk (Mk := Mk) hM σ hu hv]; simp



/-- B1b (Mk-general form of `card_crownAtoms_le`). -/
theorem card_crownAtoms_leMk {Mk : Set (CLVineG γ _)} : (crownAtoms (γ := γ) (Mk := Mk) σ).card ≤ (unitBlocks γ (Mk := Mk) S σ).length := by
  classical
  have : crownAtoms (γ := γ) (Mk := Mk) σ ⊆ ((unitBlocks γ (Mk := Mk) S σ).map fun u => u.upper).toFinset := by
    intro v hv
    simp only [crownAtoms, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    have hn : (stSt γ (Mk := Mk) S σ).cls v ≠ none := by rw [hv]; simp
    have : ∃ u ∈ unitBlocks γ (Mk := Mk) S σ, v ∈ u.atoms := by
      by_contra h
      push Not at h
      exact hn (stSt_cls_noneMk (Mk := Mk) hM σ h)
    obtain ⟨u, hu, hvu⟩ := this
    rw [stSt_cls_memMk (Mk := Mk) hM σ hu hvu] at hv
    have : u.upper = v := Option.some.inj hv
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨u, hu, this⟩)
  refine (Finset.card_le_card this).trans ?_
  exact (List.toFinset_card_le _).trans (by simp)


/-- B1b (Mk-general form of `two_mul_units_le`). -/
theorem two_mul_units_leMk {Mk : Set (CLVineG γ _)} : 2 * (unitBlocks γ (Mk := Mk) S σ).length ≤ (mergedAtoms (γ := γ) (Mk := Mk) σ).card := by
  rw [card_mergedAtomsMk (Mk := Mk) hM σ]
  have : ∀ l : List (CLBlock S), (∀ u ∈ l, 2 ≤ u.atoms.card) → 2 * l.length ≤ (l.map fun u => u.atoms.card).sum := by
    intro l
    induction l with
    | nil => simp
    | cons u l ih =>
      intro h
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have := ih fun v hv => h v (List.mem_cons_of_mem _ hv)
      have := h u (List.mem_cons_self ..)
      omega
  exact this _ fun u _ => two_le_card_atoms hM u


/-- B1b (Mk-general form of `order_add_merged`). -/
theorem order_add_mergedMk {Mk : Set (CLVineG γ _)} :
    (stSt γ (Mk := Mk) S σ).G.order + (mergedAtoms (γ := γ) (Mk := Mk) σ).card = S.order + (crownAtoms (γ := γ) (Mk := Mk) σ).card := by
  classical
  set st := stSt γ (Mk := Mk) S σ
  have hord : st.G.order = (Finset.univ.filter fun v : GBranch S.tree => st.cls v = none ∨ st.cls v = some v).card := by
    rw [Garden_order_eq_card]
    rw [← Finset.card_univ, ← Finset.card_image_of_injective _ st.M.ob_inj]
    congr 1
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    exact st.M.ob_range v
  have hS : S.order = (Finset.univ.filter fun v : GBranch S.tree => st.cls v = none).card + (mergedAtoms (γ := γ) (Mk := Mk) σ).card := by
    rw [Garden_order_eq_card, ← Finset.card_univ]
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (GBranch S.tree))) (fun v => st.cls v = none)
    rw [← this]
    congr 2
  have hsplit : (Finset.univ.filter fun v : GBranch S.tree => st.cls v = none ∨ st.cls v = some v) =
      (Finset.univ.filter fun v : GBranch S.tree => st.cls v = none) ∪ crownAtoms (γ := γ) (Mk := Mk) σ := by
    ext v
    simp [crownAtoms, st]
  have hdisj : Disjoint (Finset.univ.filter fun v : GBranch S.tree => st.cls v = none) (crownAtoms (γ := γ) (Mk := Mk) σ) := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    simp only [crownAtoms, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rw [h1] at h2; simp at h2
  rw [hord, hsplit, Finset.card_union_of_disjoint hdisj]
  omega


/-- B1b (Mk-general form of `card_hinges_eq`). -/
theorem card_hinges_eqMk {Mk : Set (CLVineG γ _)} : (stSt γ (Mk := Mk) S σ).hinges.card = (crownAtoms (γ := γ) (Mk := Mk) σ).card := by
  classical
  set st := stSt γ (Mk := Mk) S σ
  unfold SpState.hinges
  rw [← Finset.card_image_of_injective _ st.M.ob_inj]
  congr 1
  ext v
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, crownAtoms]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rcases (st.M.ob_range (st.M.ob c)).mp ⟨c, rfl⟩ with h | h
    · exact absurd h hc
    · exact h
  · intro h
    have hr : ∃ c, st.M.ob c = v := (st.M.ob_range v).mpr (Or.inr h)
    obtain ⟨c, hc⟩ := hr
    exact ⟨c, by rw [hc, h]; simp, hc⟩


/-- B1b (Mk-general form of `order_add_hinges_le`). -/
theorem order_add_hinges_leMk {Mk : Set (CLVineG γ _)} : (stSt γ (Mk := Mk) S σ).G.order + (stSt γ (Mk := Mk) S σ).hinges.card ≤ S.order := by
  have h1 := order_add_mergedMk (Mk := Mk) hM σ
  have h2 := card_hinges_eqMk (Mk := Mk) hM σ
  have h3 := card_crownAtoms_leMk (Mk := Mk) hM σ
  have h4 := two_mul_units_leMk (Mk := Mk) hM σ
  omega

/-- `n_sb + #hinges ≤ n_sk`. -/
theorem order_add_hinges_le : (stSt γ S σ).G.order + (stSt γ S σ).hinges.card ≤ S.order := order_add_hinges_leMk (Mk := ∅) hM σ

/-- B1b (Mk-general form of `order_add_units_le`). -/
theorem order_add_units_leMk {Mk : Set (CLVineG γ _)} :
    (stSt γ (Mk := Mk) S σ).G.order + ((unitBlocks γ (Mk := Mk) S σ).map fun u => u.atoms.card - 1).sum ≤ S.order := by
  have h1 := order_add_mergedMk (Mk := Mk) hM σ
  have h3 := card_crownAtoms_leMk (Mk := Mk) hM σ
  have h5 := card_mergedAtomsMk (Mk := Mk) hM σ
  have h6 : ((unitBlocks γ (Mk := Mk) S σ).map fun u => u.atoms.card - 1).sum + (unitBlocks γ (Mk := Mk) S σ).length =
      ((unitBlocks γ (Mk := Mk) S σ).map fun u => u.atoms.card).sum := by
    have : ∀ l : List (CLBlock S), (∀ u ∈ l, 2 ≤ u.atoms.card) →
        (l.map fun u => u.atoms.card - 1).sum + l.length = (l.map fun u => u.atoms.card).sum := by
      intro l
      induction l with
      | nil => simp
      | cons u l ih =>
        intro h
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        have := ih fun v hv => h v (List.mem_cons_of_mem _ hv)
        have := h u (List.mem_cons_self ..)
        omega
    exact this _ fun u _ => two_le_card_atoms hM u
  omega


end Counts
end WaveTurbulence.GammaLow.Fama.Represents
