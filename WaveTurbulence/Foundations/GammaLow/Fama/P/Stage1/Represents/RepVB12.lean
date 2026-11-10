/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a-G port of main `WaveTurbulence.Foundations.Stage1.Represents.RepVB12` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.Stage1.Represents.RepVB11
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Represents.RepVB12
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainFlows
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Famb.Vine.C.VCSigma
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
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.Step3AtH


/-!
# S2 REPRESENTS, VINE-B♯ integration: the τ-class sum with mode types depending on the type-family index

`sum_tauClass_vineD_api_dep`: VINE-C's `sum_tauClass_vineD_api` with the mode type `Ξ i` depending on `i` (the slot kernels
`slotFn(typeProfiles (U.h i))` have different mode expansions for different `i`).  Same proof, from VINE-C's
`sum_layered_eq_sum_classU` and `sum_classU_outerValM_kernel`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.VineParamContract WaveTurbulence.GammaLow.FinalCount
namespace WaveTurbulence.GammaLow.Fama.Represents
open WaveTurbulence.Represents WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.Reg.Skeleton WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.RegRed WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 TTree MeasureTheory WaveTurbulence.VineC

variable {w : ℕ} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

theorem sum_tauClass_vineD_api_dep {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) {J₀ : Type} [Fintype J₀]
    [DecidableEq J₀] {U₀ : J₀ → Finset (GBranch S.tree)} {a₀ b₀ : J₀ → GBranch S.tree}
    {R₀ : ∀ j, CLRegionData S (U₀ j) (a₀ j) (b₀ j)} {n₀ : J₀ → ℕ} (B₀ : ∀ j, Famb.VineEstS2.CLChainAssemblyΓ γ S (R₀ j) (n₀ j))
    (hdisj₀ : ∀ j j', j ≠ j' → Disjoint (U₀ j) (U₀ j')) (hprime : IsPrimeGarden S) {p : ℕ} {kind : Bool}
    (T : Finset (LayeredGarden w))
    (hT : (T : Set (LayeredGarden w)) = (Famb.VineC.unitsStartΓ B₀ hdisj₀ D hS layer hLayer).allCoreOutputs (p := p) (kind := kind))
    (V : LayeredGarden w → ℂ) {I : Type*} [Fintype I] (sgn : I → ℂ) {Ξ : I → Type*} (Wt : ∀ i, Ξ i → ℂ) {d : ℕ}
    (G : Garden w) (L γ δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ)
    (lay : GBranch G.tree → ℕ) (hinges : Finset (GBranch G.tree)) (Zw : GenDecoration G d roots 0 → ℝ)
    (hG : G.IsPlain) (amp : ∀ i, Ξ i → ReplacementSlot G → Mom d → ℂ) (frq : ∀ i, Ξ i → ReplacementSlot G → Fin 2 → ℤ)
    (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J₀) (hclk : J₀ → Fin 3 → ClkSrc G)
    (hmom : J₀ → Fin 4 → GNode G.tree) (F : I → J₀ → ℕ → Mom d → ℝ)
    (hV : ∀ y ∈ classU (Famb.VineC.unitsSplitΓ B₀) p kind (Famb.VineC.unitsStartΓ B₀ hdisj₀ D hS layer hLayer) (Famb.VineC.unitsRegionΓ B₀ hdisj₀),
      V y.1.layered = ∑ i, sgn i * ∑' ξ : Ξ i, Wt i ξ *
        outerValM G L γ δ base roots tt lay hinges Zw hG (amp i ξ) (frq i ξ) route hclk hmom
          (fun j lam t k => unitRecenteredW y.1 (y.2 j) L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2)
            (k 0) (k 1) (k 2) (k 3)))
    (hξ : ∀ i, ∀ y ∈ classU (Famb.VineC.unitsSplitΓ B₀) p kind (Famb.VineC.unitsStartΓ B₀ hdisj₀ D hS layer hLayer) (Famb.VineC.unitsRegionΓ B₀ hdisj₀),
      Summable (fun ξ : Ξ i => Wt i ξ *
        outerValM G L γ δ base roots tt lay hinges Zw hG (amp i ξ) (frq i ξ) route hclk hmom
          (fun j lam t k => unitRecenteredW y.1 (y.2 j) L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2)
            (k 0) (k 1) (k 2) (k 3))))
    (hint : ∀ i (ξ : Ξ i), ∀ y ∈ classU (Famb.VineC.unitsSplitΓ B₀) p kind (Famb.VineC.unitsStartΓ B₀ hdisj₀ D hS layer hLayer)
        (Famb.VineC.unitsRegionΓ B₀ hdisj₀), ∀ z,
      Integrable (outerIntegrandM G L γ δ base roots tt lay hG (amp i ξ) (frq i ξ) route hclk hmom
        (fun j lam t k => unitRecenteredW y.1 (y.2 j) L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2)
          (k 0) (k 1) (k 2) (k 3)) z))
    (hsm : ∀ i (ξ : Ξ i), ∀ y ∈ classU (Famb.VineC.unitsSplitΓ B₀) p kind (Famb.VineC.unitsStartΓ B₀ hdisj₀ D hS layer hLayer)
        (Famb.VineC.unitsRegionΓ B₀ hdisj₀),
      Summable (fun z : GenDecoration G d roots 0 =>
        (splicedEpsilon G hinges z.1 : ℂ) * (Zw z : ℂ) *
          ∫ τ, outerIntegrandM G L γ δ base roots tt lay hG (amp i ξ) (frq i ξ) route hclk hmom
            (fun j lam t k => unitRecenteredW y.1 (y.2 j) L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2)
              (k 0) (k 1) (k 2) (k 3)) z τ)) :
    ∑ LG ∈ T, V LG = ∑ i, sgn i * ∑' ξ : Ξ i, Wt i ξ *
      outerValM G L γ δ base roots tt lay hinges Zw hG (amp i ξ) (frq i ξ) route hclk hmom
        (fun j lam t k => VineEstS5C.Cont.twistedRecenteredModC S (a₀ j)
          (canonFinsetK p kind (Famb.VineEstS4.startStateΓ (B₀ j) D hS layer hLayer) (Famb.VineEstS4.chainStartΓ (B₀ j)))
          L γ δ (F i j) base lam (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) := by
  rw [sum_layered_eq_sum_classU (Us := Famb.VineC.unitsSplitΓ B₀) (A := Famb.VineC.unitsStartΓ B₀ hdisj₀ D hS layer hLayer) hprime
    (Famb.VineC.unitsRegionΓ B₀ hdisj₀) T hT V, Finset.sum_congr rfl hV, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, ← Summable.tsum_finsetSum (hξ i)]
  congr 1
  refine tsum_congr fun ξ => ?_
  rw [← Finset.mul_sum]
  congr 1
  rw [sum_classU_outerValM_kernel (Us := Famb.VineC.unitsSplitΓ B₀) (p := p) (kind := kind)
    (A := Famb.VineC.unitsStartΓ B₀ hdisj₀ D hS layer hLayer) hprime (Famb.VineC.unitsRegionΓ B₀ hdisj₀) G L γ δ base roots tt lay hinges Zw hG
    (amp i ξ) (frq i ξ) route hclk hmom (F i) (hint i ξ) (hsm i ξ)]
  congr 1
  funext j lam t k
  exact (twistedRecenteredModC_eq_W _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).symm

end WaveTurbulence.GammaLow.Fama.Represents
