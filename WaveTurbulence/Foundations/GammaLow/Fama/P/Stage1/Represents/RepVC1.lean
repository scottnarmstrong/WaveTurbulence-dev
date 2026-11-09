/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Represents.RepVC1` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstGamma
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.Stage1.Represents.RepUG10
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Represents.RepVC1
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
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Skip
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.SurvData
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepE2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNV2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNV3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNV4
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine4
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine5
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVN11
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVN12
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
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
# S2 REPRESENTS, session 11: the hinge-data constant depends only on `d` and `η`

`hinge_units_const` is `exists_hinge_data_units_leaf_w` with the constant `C` chosen before the parameters `P`
(it depends only on `d`, `η`), so that F-CONST (`C₁ ≥ Cchi·ball·(9K)²·Ch`) is not circular.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.VineParamContract WaveTurbulence.GammaLow.FinalCount
namespace WaveTurbulence.GammaLow.Fama.Represents
open WaveTurbulence.Represents WaveTurbulence.GammaLow.FinalCount
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RepAnalytic WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C VineParamContract

variable {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]
open scoped ENNReal Classical WaveTurbulence.GammaLow.FinalCount

theorem hinge_units_const (d : ℕ) (η : ℝ) (hη : 0 ≤ η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : WTParams) [Fact (P.γ ≤ 1 / 2)], P.d = d → P.η = η → Famb.VineEstGammaHalfMK P → 0 ≤ P.C₁ → 0 < P.L →
      ∀ {p : ℕ}, p < P.D → ∀ {w : ℕ} {S : Garden w} (hprime : IsPrimeGarden S) (hM9 : Famb.NormalChartSupply P.γ)
      (RD : ReconstructionData S) (hG : S.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
      (hLayer : IsLayering (RD.garden hG) layer) (hcan : IsCanonGC (p + 1) (layeredReconstruction RD hG layer hLayer))
      (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4)
      {J : Type} [Fintype J] {U₀ : J → Finset (GBranch S.tree)} {a₀ b₀ : J → GBranch S.tree}
      {R₀ : ∀ j, CLRegionData S (U₀ j) (a₀ j) (b₀ j)} {n₀ : J → ℕ} (B₀ : ∀ j, Famb.VineEstS2.CLChainAssemblyΓ P.γ S (R₀ j) (n₀ j))
      (hcl : ∀ j, clLocalOrder1 (R₀ j) ≤ P.N 1 ^ 4)
      (h : J → ℕ → Mom P.d → ℝ) (bb : J → ℝ) (hbb : ∀ j, 0 ≤ bb j)
      (hh : ∀ j, ∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (h j r) ≤ ENNReal.ofReal (bb j))
      (centre : J → (Fin 4 → Fin P.d → ℤ) → Fin 4 → Mom P.d) (base : Mom P.d)
      (hq : ∀ j, qOutOf RD hG layer (a₀ j) (b₀ j) (R₀ j) 1 ≤ qOutOf RD hG layer (a₀ j) (b₀ j) (R₀ j) 0 ∧
        qOutOf RD hG layer (a₀ j) (b₀ j) (R₀ j) 2 ≤ qOutOf RD hG layer (a₀ j) (b₀ j) (R₀ j) 0)
      (hcont : ∀ j c (lam : ℤ), ∀ E ∈ outSet (unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base) P.L P.γ P.η,
        ContinuousOn (fun t => unitHk P p (B₀ j) RD hG layer hLayer (h j) base lam t
          (sumintBoundary (S.sign (a₀ j).toNode) E))
          (cubeSet (unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base).qOut))
      (Gsb : Garden w) (tt : Fin w → ℝ) (roots : Fin w → Fin P.d → ℤ)
      (selSk : GenDecoration Gsb P.d roots 0 → Prop) (lay : GBranch Gsb.tree → ℕ)
      (hmom : J → Fin 4 → GNode Gsb.tree) (hclk : J → Fin 3 → ClkSrc Gsb)
      (leaf : J → Fin 3 → Prop) (td : J → Fin 3 → ℝ)
      (hind : ∀ j (lam : ℤ) (t t' : Fin 3 → ℝ) (k : Fin 4 → Mom P.d), (∀ i, ¬ leaf j i → t i = t' i) →
        unitHk P p (B₀ j) RD hG layer hLayer (h j) base lam t k =
          unitHk P p (B₀ j) RD hG layer hLayer (h j) base lam t' k),
      (∀ κ : GenDecoration Gsb P.d roots 0, selSk κ → ∀ τ ∈ splicedTimeDomain Gsb lay tt, ∀ j c,
        (∀ i, ‖(base + latticePoint P.L (κ.1 (hmom j i))) - latPt P.d (c i)‖ ≤ 1) →
          (fun i => if leaf j i then td j i else clockOf Gsb tt τ (hclk j i)) ∈
            outBoxW (unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base)) →
      (∀ κ : GenDecoration Gsb P.d roots 0, selSk κ → ∀ j c,
        (∀ i, ‖(base + latticePoint P.L (κ.1 (hmom j i))) - latPt P.d (c i)‖ ≤ 1) →
          sumintBoundary (S.sign (a₀ j).toNode) (fun i => base + latticePoint P.L (κ.1 (hmom j i))) ∈
            outSet (unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base) P.L P.γ P.η) →
      ∀ lam : J → ℤ, ∃ (H : HingeFam J P.d) (Mh : J → ℝ), (∀ j c', ∑' l, H.w j c' l ≤ Mh j) ∧
        (∀ κ : GenDecoration Gsb P.d roots 0, selSk κ → ∀ τ ∈ splicedTimeDomain Gsb lay tt, ∀ j c',
          (∀ i, ‖(base + latticePoint P.L (κ.1 (hmom j i))) - latPt P.d (c' i)‖ ≤ 1) →
          HasSum (fun l => (H.w j c' l : ℂ) * H.a j c' l (fun i => base + latticePoint P.L (κ.1 (hmom j i))) *
            fsPhase (H.m j c' l) (fun i => clockOf Gsb tt τ (hclk j i)))
            (unitHk P p (B₀ j) RD hG layer hLayer (h j) base (lam j) (fun i => clockOf Gsb tt τ (hclk j i))
              (fun i => base + latticePoint P.L (κ.1 (hmom j i))))) ∧
        ∏ j, Mh j = C ^ Fintype.card J *
          (∏ j, unitMass P hM9 (B₀ j) RD hG layer hLayer (bb j)) *
          ∏ j, (1 + |((lam j : ℤ) : ℝ)|) ^ (6 * P.η ^ 6) := by
  obtain ⟨C, hC, hex⟩ := exists_hinge_data_mod_ck_w (θ := 2 * η ^ 8) (by positivity) d
  refine ⟨C, hC, fun P _ hPd hPη hV hC₁ hL0 {p} hp {w} {S} hprime hM9 RD hG layer hLayer hcan hord {J} _ {U₀} {a₀} {b₀} {R₀} {n₀} B₀ hcl h bb hbb hh
    centre base hq hcont Gsb tt roots selSk lay hmom hclk leaf td hind G1 G2 lam => ?_⟩
  subst hPd hPη
  have hM0 : ∀ j, 0 ≤ unitMass P hM9 (B₀ j) RD hG layer hLayer (bb j) := fun j =>
    mul_nonneg (mul_nonneg (pow_nonneg (mul_nonneg hC₁ (Real.sqrt_nonneg _)) _) (Real.rpow_nonneg hL0.le _))
      (WaveTurbulence.VineEstS5C.regionLeafSize_const_nonneg RD hG (R₀ j) layer hLayer (hbb j))
  obtain ⟨H, Mh, hMh, hsum, hprod⟩ := hex Gsb J (fun j c => unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base)
    (fun j c => outSet (unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base) P.L P.γ P.η)
    (fun j => S.sign (a₀ j).toNode) (fun j lam t k => unitHk P p (B₀ j) RD hG layer hLayer (h j) base lam t k)
    (fun j => unitMass P hM9 (B₀ j) RD hG layer hLayer (bb j)) (6 * P.η ^ 6) hM0
    (fun j c' => hq j) hcont (fun j c lam => by
      have := unit_vineest_bound hV hp (h j) (bb j) (hbb j) (hh j) hprime hM9 (B₀ j) RD hG layer hLayer hcan hord
        (hcl j) (centre j c) base (lam : ℝ)
      have hM := step3D_M₁_const hM9 (B₀ j) RD hG layer hLayer (centre j c) (fun _ => (0 : Mom P.d)) base 0
      refine le_of_le_of_eq this ?_
      unfold unitMass
      rw [hM]) P.L base tt roots selSk lay hmom
    (fun j τ i => if leaf j i then td j i else clockOf Gsb tt τ (hclk j i)) G1 G2 lam
  refine ⟨H.leafWrap leaf td, Mh, hMh, fun κ hκ τ hτ j c' hball => ?_, hprod⟩
  have h1 := hsum κ hκ τ hτ j c' hball
  rw [hind j (lam j) _ (fun i => clockOf Gsb tt τ (hclk j i)) _ (fun i hi => by simp [hi])] at h1
  exact H.leafWrap_hasSum leaf td j c' _ (fun i => clockOf Gsb tt τ (hclk j i)) h1


end WaveTurbulence.GammaLow.Fama.Represents
