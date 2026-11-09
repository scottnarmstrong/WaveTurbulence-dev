/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Represents.RepPr3` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepPr2
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Represents.RepPr3
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePlainA4
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescribedPoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineReindex
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport


/-!
# S2 REPRESENTS: the producer, part 3 (`Stage1Partition`)

`stage1Partition_prod`: the coarse classes partition `A`, and every garden of a class carries, for every decoration,
exactly one piece whose selection holds (the `σ` of the decoration, TARGET L1950, and the tau class of that prescribed
point).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.VineParamContract WaveTurbulence.GammaLow.FinalCount
namespace WaveTurbulence.GammaLow.Fama.Represents
open WaveTurbulence.Represents WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence WaveTurbulence.VineA WaveTurbulence.LGSpine WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.VineA.PrescribedPrimeGarden

variable {R : ℕ} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- Two prescribed points over the same garden whose `σ` both holds at `κ` coincide. -/
theorem eq_of_selAt (P : WTParams) (base : Mom P.d) {roots : Fin (2 * R) → (Fin P.d → ℤ)}
    (LG : LayeredGarden (2 * R)) (κ : GenDecoration LG.garden P.d roots 0)
    (b b' : VineA.PrescribedPrimeGarden γ (2 * R)) (h : b.layered = LG) (h' : b'.layered = LG)
    (hs : selAt γ P base b.prime b.sigma (h ▸ κ)) (hs' : selAt γ P base b'.prime b'.sigma (h' ▸ κ)) : b = b' := by
  subst h
  rcases b with ⟨LG1, pr1, σ1⟩
  rcases b' with ⟨LG2, pr2, σ2⟩
  change LG2 = LG1 at h'
  subst h'
  have e : pr1 = pr2 := primeData_unique _ _
  subst e
  have : σ1 = σ2 := VineA.NormalizedSplice.selOf_unique P.L P.γ P.η base _ hs hs'
  subst this
  rfl

/-- B1b-2 (Mk-general form of `stage1Partition_prod`): the coarse′ classes (coarse marking `mkC`) partition `A`, and every
garden of a class carries, for every decoration, exactly one fine′ piece (fine marking `mkF ⊇ mkC`) whose selection holds.
Hypotheses: the coarse marking is carried by every batch (the world's `markInvariantBatchV_markI0`) and lies below the
fine marking (`Π₀ ⊆ Π`).  The selection `selAt` is the decoration's own `σ` (unchanged, B1a D5): this statement does not
read the gap specification (ruling R171). -/
theorem stage1Partition_prodMk (p : ℕ) (kind : Bool) (A : Finset (LayeredGarden (2 * R)))
    (hplain : ∀ LG ∈ A, LG.garden.IsPlain) (P : WTParams) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) {mkF mkC : Stage1Mk.MarkFn γ (2 * R)}
    (hV : Stage1Mk.MarkInvariantBatchV γ mkC fun _ => True)
    (hsub : ∀ {LG : LayeredGarden (2 * R)} (B : VineA.PrimeData LG), mkC B ⊆ mkF B) :
    Stage1Partition roots A (membersP γ (p := p) (kind := kind) (A := A) (mk := mkC)) (clsPMk γ (mkF := mkF) mkC)
      (selPMk γ p kind A P base roots mkF) := by
  classical
  refine ⟨fun LG => ⟨fun hLG => ?_, fun ⟨c, hc⟩ => (Finset.mem_filter.1 hc).1⟩, ?_, ?_⟩
  · have hp := hplain LG hLG
    let b0 : VineA.PrescribedPrimeGarden γ (2 * R) := ⟨LG, primeDataOf LG hp, fun _ => .ZG⟩
    refine ⟨⟨coarseOf γ p kind b0 mkC, ⟨⟨b0, hLG⟩, rfl⟩⟩, Finset.mem_filter.2 ⟨hLG, ?_⟩⟩
    exact VineA.PrimeData.mem_coarse_outputs_selfMk b0.prime (mkC b0.prime)
  · rintro ⟨_, ⟨x, rfl⟩⟩ ⟨_, ⟨x', rfl⟩⟩ hne
    rcases VineA.PrimeData.coarse_outputs_disjoint_or_eqMk (p := p) (kind := kind) hV x.1.prime x'.1.prime with hd | he
    · rw [Finset.disjoint_left]
      intro LG h1 h2
      exact Set.disjoint_left.1 hd (Finset.mem_filter.1 h1).2 (Finset.mem_filter.1 h2).2
    · exact (hne (Subtype.ext he)).elim
  · intro c LG hLG κ
    obtain ⟨hLGA, hLGc⟩ := Finset.mem_filter.1 hLG
    have hp := hplain LG hLGA
    obtain ⟨σ0, hσ0, hu⟩ := selAt_exists_unique (γ := γ) P base (primeDataOf LG hp) κ
    let b0 : VineA.PrescribedPrimeGarden γ (2 * R) := ⟨LG, primeDataOf LG hp, σ0⟩
    let π0 : PcA γ R p kind A mkF := Quotient.mk _ (⟨b0, hLGA⟩ : PtA γ R A)
    have hrel0 : VineA.PrescribedPrimeGarden.Related γ (p := p) (kind := kind) (repPt γ π0) b0 mkF :=
      Quotient.mk_out (s := ptSetoid γ p kind A mkF) ⟨b0, hLGA⟩
    have hsel0 : selPMk γ p kind A P base roots mkF π0 LG κ := ⟨b0, rfl, hrel0, hσ0⟩
    refine ⟨π0, ⟨?_, hsel0⟩, ?_⟩
    · obtain ⟨_, ⟨z, rfl⟩⟩ := c
      refine Subtype.ext ?_
      change coarseOf γ p kind (repPt γ π0) mkC = coarseOf γ p kind z.1 mkC
      rw [coarse_eq_of_relatedMk hV hsub hrel0]
      have hLGc' : LG ∈ coarseOf γ p kind z.1 mkC := hLGc
      exact (VineA.PrimeData.coarse_outputs_rebaseMk (p := p) (kind := kind) hV z.1.prime b0.prime hLGc').symm
    · intro π' ⟨_, b, h, hrel, hs⟩
      have hbb : b = b0 := eq_of_selAt P base LG κ b b0 h rfl hs hσ0
      subst hbb
      rw [← Quotient.out_eq π', ← Quotient.out_eq π0]
      exact Quotient.sound (Relation.EqvGen.trans _ _ _ hrel (Relation.EqvGen.symm _ _ hrel0))

theorem stage1Partition_prod (p : ℕ) (kind : Bool) (A : Finset (LayeredGarden (2 * R)))
    (hplain : ∀ LG ∈ A, LG.garden.IsPlain) (P : WTParams) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) :
    Stage1Partition roots A (membersP γ (p := p) (kind := kind) (A := A)) (clsP γ) (selP γ p kind A P base roots) :=
  stage1Partition_prodMk p kind A hplain P base roots (mkF := fun _ => ∅) (mkC := fun _ => ∅)
    (Stage1Mk.markInvariantBatchV_empty fun _ => True) (fun _ => subset_rfl)

end WaveTurbulence.GammaLow.Fama.Represents
