/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (with L5a's porter) of main `WaveTurbulence.Foundations.Stage1.Geometry.SubproFinalR83` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproCross3R83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproSupportAR83
public import WaveTurbulence.Foundations.FinalCount.SubproTame
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproFinalR83
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
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproObjMap
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproContained2R83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproContainedR83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproCross2R83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproCrossIsoR83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproCrossR83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproCrownR83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproEntry2R83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproEntryR83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproGap2R83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproItems2R83
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineChainNoCN
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCoarseGroupCode
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineDVGroupKey
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupPickCarrier
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupPickSpec
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineHVGroupKey
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizationNames
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedPiece
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceGap
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.VineNormalizedRedSpliceGapKind
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceHingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceObj2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSplicePairs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
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
-- R83 port of sp-src/SubproFinal.lean (FLOWER-P6 R83): successor designations, see HANDOFF


/-!
# SUBPRO (S4): TARGET Prop `subpro` (L2040-L2051) for the construction of S2a (R28, atom-set form)

`subproSupportA`: on the support of the epsilon and gap factors, `SubproSupportA` (the six conclusions of `subpro`, with
`contained` and `crossing` in the atom-set form of TARGET's "subset", R28 ruling 3) holds for `G_sb`, `C_1`, the hinges and
the hinge pairs of `Fama.VineA.NormalizedSplice.stage1PieceOf`.  `SubproObligationA` is the atom-set version of `Fama.SubproObligation`;
`subproObligationA` discharges it (needs `P.L ≠ 0`, R28 ruling 4).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.Subpro.VineA.NormalizedSplice.Subpro
open WaveTurbulence.VineA.NormalizedSplice.Subpro WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Fama.VineA WaveTurbulence.GammaLow.Fama.VineA.NormalizedSplice WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.Stage1

variable {R : ℕ} {G : Garden (2 * R)} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- **`subpro` (2)-(6) for the construction, for one decoration.** -/
theorem subproSupportA (σ : Prescription G) {d : ℕ}
    (D : SplicedKernelData (stSt γ G σ).G d) (hD : D.gapSpecification = Fama.VineA.NormalizedSplice.gapSpecification γ G σ)
    (hpl : (stSt γ G σ).G.IsPlain) {L : ℝ} (hL : L ≠ 0) (γ' η : ℝ) (base : Mom d)
    (roots : Fin (2 * R) → (Fin d → ℤ)) (z : GenDecoration (stSt γ G σ).G d roots 0)
    (hε : splicedEpsilon (stSt γ G σ).G (Fama.VineA.NormalizedSplice.collectionChoices γ G σ).hinges z.1 ≠ 0)
    (hZ : splicedGapIndicator (stSt γ G σ).G D L γ' η base z.1 ≠ 0) :
    SubproSupportA γ (stSt γ G σ).G (Fama.VineA.NormalizedSplice.collectionChoices γ G σ) L γ' η base
      (Finset.univ.image (fun i => base + latticePoint L (roots i))) (bondIndex (stSt γ G σ).G z.1) := by
  have hdec := sbDec_of_gen σ hpl hL base roots z
  have hM : G.molecule.IsMolecule := WaveTurbulence.Mole.garden_isMolecule G
  refine ⟨selectedSG_cc2 σ D hD L γ' η base z.1 hZ hdec, ?_, contained_support σ D hD L γ' η base z.1 hZ,
    hingeSG_cc2 σ D hD L γ' η base z.1 hZ hdec, hingeJoint_cc2 σ, ?_⟩
  · intro v hv hg
    exact tame_of_eps (stSt γ G σ).G hpl hL base roots z hε hv hg
  · intro P _ hout hnd
    have hout' : ∀ O ∈ Fama.VineA.NormalizedSplice.objects γ G σ, ¬ P.atoms ⊆ O.atoms := by
      intro O hO
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hO
      have := hout i
      simp only [Fama.VineA.NormalizedSplice.collectionChoices] at this
      rw [hi] at this
      exact this
    exact crossing_atoms hM σ P hout' hnd

end WaveTurbulence.GammaLow.Famc.Subpro.VineA.NormalizedSplice.Subpro
