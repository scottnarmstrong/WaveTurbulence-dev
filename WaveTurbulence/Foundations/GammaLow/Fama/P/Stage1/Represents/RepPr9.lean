/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Represents.RepPr9` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepPr8
public import WaveTurbulence.Foundations.Stage1.Geometry.RedSpliceCoverThm
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Represents.RepPr9
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
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepPr1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepPr2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepPr5
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCoarseGardenPartition
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCoarseGroupCode
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineDVGroupKey
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamilyUnique
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineBatch
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineOperation
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineRebase
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineRecovery
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineRefinement
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupExtension
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupPickCarrier
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupPickSpec
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineHVGroupKey
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkFn
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkedClasses
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizationNames
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedPiece
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceHingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceObj2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSplicePairs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePlainA4
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescribedPoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineReindex
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitCover


/-!
# S2 REPRESENTS: the class-member sum of a vine-free piece is a single garden's value

For a piece `π` whose representative point `b` has no unit (`unitBlocks γ b.prime.skeleton b.totalSigma = []`), `vinesV0` is empty, so
the fine tau class of `b` is `{b.layered}` (`outputs_subset_of_unitBlocks_nil`), the selection `selP γ π` is supported on `b.layered`
and equals `selAt` there (`Related` preserves the normalized code, `eq_of_layered_code`), and
`Σ_{LG ∈ members} F.valueSel LG (selP γ π LG) = F.valueSel b.layered (selAt …)`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.VineParamContract WaveTurbulence.GammaLow.FinalCount
namespace WaveTurbulence.GammaLow.Fama.Represents
open WaveTurbulence.Represents WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence TTree WaveTurbulence.LGSpine WaveTurbulence.RedSplice WaveTurbulence.Reg WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed Set WaveTurbulence.VineA WaveTurbulence.LFTwist WaveTurbulence.VineA.PrescribedPrimeGarden





variable {R : ℕ} {p : ℕ} {kind : Bool} {A : Finset (LayeredGarden (2 * R))} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- B1b-2 (Mk-general form of `selP_noVine`): over a representative without units at the fine marking (carried by
every fine batch), the fine′ selection is `selAt` on its garden and false elsewhere. -/
theorem selP_noVineMk (P : WTParams) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    {mk : Stage1Mk.MarkFn γ (2 * R)} (hT : ∀ c : VineA.PrescribedPrimeGarden γ (2 * R), c.FineTransportedAt γ mk)
    (π : PcA γ R p kind A mk)
    (hnv : unitBlocks γ (repPt γ π).prime.skeleton (repPt γ π).totalSigma (mk (repPt γ π).prime) = [])
    (LG : LayeredGarden (2 * R)) (κ : GenDecoration LG.garden P.d roots 0) :
    selPMk γ p kind A P base roots mk π LG κ ↔
      ∃ h : (repPt γ π).layered = LG, selAt γ P base (repPt γ π).prime (repPt γ π).sigma (h ▸ κ) := by
  constructor
  · rintro ⟨b', h, hrel, hs⟩
    have hbb : b' = repPt γ π := VineA.PrescribedPrimeGarden.related_eq_of_unitBlocks_nil hT hnv hrel
    subst hbb
    exact ⟨h, hs⟩
  · rintro ⟨h, hs⟩
    exact ⟨repPt γ π, h, Relation.EqvGen.refl _, hs⟩

/-- B1b-2 (Mk-general form of `noVine_members_sum`): the coarse′ class sum of a unit-free fine′ piece. -/
theorem noVine_members_sumMk (P : WTParams) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (tt : Fin (2 * R) → ℝ) (F : LeafFamily P (2 * R)) {mkF : Stage1Mk.MarkFn γ (2 * R)} (mkC : Stage1Mk.MarkFn γ (2 * R))
    (hT : ∀ c : VineA.PrescribedPrimeGarden γ (2 * R), c.FineTransportedAt γ mkF) (π : PcA γ R p kind A mkF)
    (hnv : unitBlocks γ (repPt γ π).prime.skeleton (repPt γ π).totalSigma (mkF (repPt γ π).prime) = []) :
    ∑ LG ∈ membersP γ (clsPMk γ mkC π), F.valueSel tt base roots LG (selPMk γ p kind A P base roots mkF π LG) =
      F.valueSel tt base roots (repPt γ π).layered (fun κ => selAt γ P base (repPt γ π).prime (repPt γ π).sigma κ) := by
  classical
  have hmem : (repPt γ π).layered ∈ membersP γ (clsPMk γ mkC π) :=
    Finset.mem_filter.2 ⟨repPt_layered_memMk π, VineA.PrimeData.mem_coarse_outputs_selfMk (repPt γ π).prime (mkC (repPt γ π).prime)⟩
  rw [Finset.sum_eq_single (repPt γ π).layered]
  · congr 1
    funext κ
    exact propext ((selP_noVineMk P base roots hT π hnv _ κ).trans ⟨fun ⟨h, hs⟩ => hs, fun hs => ⟨rfl, hs⟩⟩)
  · intro LG _ hne
    have hnone : ∀ κ : GenDecoration LG.garden P.d roots 0, ¬ selPMk γ p kind A P base roots mkF π LG κ := by
      intro κ hκ
      obtain ⟨h, -⟩ := (selP_noVineMk P base roots hT π hnv LG κ).1 hκ
      exact hne h.symm
    simp [LeafFamily.valueSel, kernelLeavesSel, hnone]
  · intro h; exact absurd hmem h


theorem noVine_members_sum (P : WTParams) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (tt : Fin (2 * R) → ℝ) (F : LeafFamily P (2 * R)) (π : PcA γ R p kind A)
    (hnv : unitBlocks γ (repPt γ π).prime.skeleton (repPt γ π).totalSigma = []) :
    ∑ LG ∈ membersP γ (clsP γ π), F.valueSel tt base roots LG (selP γ p kind A P base roots π LG) =
      F.valueSel tt base roots (repPt γ π).layered (fun κ => selAt γ P base (repPt γ π).prime (repPt γ π).sigma κ) :=
  noVine_members_sumMk (mkF := fun _ => ∅) P base roots tt F (fun _ => ∅)
    VineA.PrescribedPrimeGarden.fineTransportedAt_empty π hnv

end WaveTurbulence.GammaLow.Fama.Represents
