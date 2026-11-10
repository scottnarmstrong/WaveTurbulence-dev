/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Represents.RepPr2` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepPr1
public import WaveTurbulence.Foundations.Stage1.Represents.RepCountB
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkedClasses
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Represents.RepPr2
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
# S2 REPRESENTS: the producer, part 2 (carrier and `Stage1Partition`)

For a finite set `A` of plain layered gardens: the prescribed points `PtA` over `A`, the pieces `PcA` = fine tau classes
of prescribed points (`VineA.PrescribedPrimeGarden.Related`, the equivalence of VINE-A's `VineA.PrescribedPrimeGarden.Related`), the coarse classes `ClA`
(`VineA.PrimeData.coarseState.allCoreOutputs`), `members c = A ∩ c`, and the selection
`selP γ π LG κ := ∃ b over LG, b ~ rep π ∧ selAt γ b κ` (TARGET L1950: `σ`-restriction and tau class).

B1a (ruling F-1): the fine classes (`ptSetoid`, `PcA`, `repPt`, `selP`) take the trailing fine marking `mk` and the
coarse classes (`coarseOf`, `ClA`, `membersP`) the coarse marking (both default `fun _ => ∅`); `clsP` maps fine to
coarse classes.  At the default they are main's (`coarseOf_empty`).
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

theorem finite_groupPrescription {w : ℕ} (G : Garden w) : Finite (GroupPrescription γ G) := by
  classical
  have hfin : (maximalGroupsG γ G.molecule).Finite := Set.toFinite _
  have : Finite (maximalGroupsG γ G.molecule) := hfin
  have : Finite Molecule.GapKind := inferInstance
  unfold GroupPrescription
  infer_instance

/-- Prescribed points over `A`. -/
abbrev PtA (γ : ℝ) [Fact (γ ≤ 1 / 2)] (R : ℕ) (A : Finset (LayeredGarden (2 * R))) := {b : VineA.PrescribedPrimeGarden γ (2 * R) // b.layered ∈ A}

theorem finite_ptA (A : Finset (LayeredGarden (2 * R))) : Finite (PtA γ R A) := by
  classical
  let T : LayeredGarden (2 * R) → Set (VineA.PrescribedPrimeGarden γ (2 * R)) := fun LG =>
    ⋃ hp : LG.garden.IsPlain, Set.range (fun σ : GroupPrescription γ (primeDataOf LG hp).skeleton =>
      (⟨LG, primeDataOf LG hp, σ⟩ : VineA.PrescribedPrimeGarden γ (2 * R)))
  have hf : Set.Finite {b : VineA.PrescribedPrimeGarden γ (2 * R) | b.layered ∈ A} := by
    refine Set.Finite.subset (Set.Finite.biUnion (t := T) A.finite_toSet fun LG _ =>
      Set.finite_iUnion fun hp : LG.garden.IsPlain => ?_) ?_
    · have := finite_groupPrescription (γ := γ) (primeDataOf LG hp).skeleton
      exact Set.finite_range _
    · rintro ⟨LG, pr, σ⟩ hb
      have hp : LG.garden.IsPlain := pr.decodes.1
      have e : pr = primeDataOf LG hp := primeData_unique _ _
      subst e
      exact Set.mem_biUnion (x := LG) hb (Set.mem_iUnion.2 ⟨hp, ⟨σ, rfl⟩⟩)
  exact hf.to_subtype

def ptSetoid (γ : ℝ) [Fact (γ ≤ 1 / 2)] (p : ℕ) (kind : Bool) (A : Finset (LayeredGarden (2 * R)))
    (mk : Stage1Mk.MarkFn γ (2 * R) := fun _ => ∅) : Setoid (PtA γ R A) where
  r a b := VineA.PrescribedPrimeGarden.Related γ (p := p) (kind := kind) a.1 b.1 mk
  iseqv := ⟨fun a => (Relation.EqvGen.is_equivalence _).refl a.1,
    fun h => (Relation.EqvGen.is_equivalence _).symm h,
    fun h h' => (Relation.EqvGen.is_equivalence _).trans h h'⟩

/-- The pieces: fine tau classes of prescribed points over `A`. -/
abbrev PcA (γ : ℝ) [Fact (γ ≤ 1 / 2)] (R : ℕ) (p : ℕ) (kind : Bool) (A : Finset (LayeredGarden (2 * R)))
    (mk : Stage1Mk.MarkFn γ (2 * R) := fun _ => ∅) :=
  Quotient (ptSetoid γ (R := R) p kind A mk)

noncomputable instance (p : ℕ) (kind : Bool) (A : Finset (LayeredGarden (2 * R))) (mk : Stage1Mk.MarkFn γ (2 * R)) :
    Fintype (PcA γ R p kind A mk) :=
  have := finite_ptA (γ := γ) A
  have : Finite (PcA γ R p kind A) := Quotient.finite _
  Fintype.ofFinite _

/-- A representative prescribed point of a piece. -/
noncomputable def repPt (γ : ℝ) [Fact (γ ≤ 1 / 2)] {p : ℕ} {kind : Bool} {A : Finset (LayeredGarden (2 * R))} {mk : Stage1Mk.MarkFn γ (2 * R)}
    (π : PcA γ R p kind A mk) : VineA.PrescribedPrimeGarden γ (2 * R) := (Quotient.out π).1

theorem repPt_layered_mem {p : ℕ} {kind : Bool} {A : Finset (LayeredGarden (2 * R))} (π : PcA γ R p kind A) :
    (repPt γ π).layered ∈ A := (Quotient.out π).2

/-- B1a: `repPt_layered_mem` for every fine marking. -/
theorem repPt_layered_memMk {p : ℕ} {kind : Bool} {A : Finset (LayeredGarden (2 * R))}
    {mk : Stage1Mk.MarkFn γ (2 * R)} (π : PcA γ R p kind A mk) : (repPt γ π).layered ∈ A := (Quotient.out π).2

/-- The coarse class of a prescribed point.  B1a: with the coarse marking `mk` (default `fun _ => ∅`), the coarse′
class of twists at the unmarked vines of `𝒱` (`VineA.coarseStateMk`). -/
def coarseOf (γ : ℝ) [Fact (γ ≤ 1 / 2)] (p : ℕ) (kind : Bool) (b : VineA.PrescribedPrimeGarden γ (2 * R)) (mk : Stage1Mk.MarkFn γ (2 * R) := fun _ => ∅) :
    Set (LayeredGarden (2 * R)) :=
  (VineA.coarseStateMk γ b.prime (mk b.prime)).allCoreOutputs (p := p) (kind := kind)


/-- The coarse classes of `A`. -/
abbrev ClA (γ : ℝ) [Fact (γ ≤ 1 / 2)] (R : ℕ) (p : ℕ) (kind : Bool) (A : Finset (LayeredGarden (2 * R)))
    (mk : Stage1Mk.MarkFn γ (2 * R) := fun _ => ∅) :=
  ↥(Set.range fun b : PtA γ R A => coarseOf γ p kind b.1 mk)

noncomputable instance (p : ℕ) (kind : Bool) (A : Finset (LayeredGarden (2 * R))) (mk : Stage1Mk.MarkFn γ (2 * R)) :
    Fintype (ClA γ R p kind A mk) :=
  have := finite_ptA (γ := γ) A
  have : Finite (ClA γ R p kind A) := (Set.finite_range _).to_subtype
  Fintype.ofFinite _

/-- B1a: the coarse′ class (coarse marking `mkC`) of a fine′ piece (fine marking `mkF`). -/
noncomputable def clsPMk (γ : ℝ) [Fact (γ ≤ 1 / 2)] {p : ℕ} {kind : Bool} {A : Finset (LayeredGarden (2 * R))} {mkF : Stage1Mk.MarkFn γ (2 * R)}
    (mkC : Stage1Mk.MarkFn γ (2 * R)) (π : PcA γ R p kind A mkF) : ClA γ R p kind A mkC :=
  ⟨coarseOf γ p kind (repPt γ π) mkC, ⟨Quotient.out π, rfl⟩⟩

/-- The coarse class of a piece (main's classes; B1a: `clsPMk` at the empty fine and coarse markings). -/
noncomputable abbrev clsP (γ : ℝ) [Fact (γ ≤ 1 / 2)] {p : ℕ} {kind : Bool} {A : Finset (LayeredGarden (2 * R))}
    (π : PcA γ R p kind A) : ClA γ R p kind A := clsPMk γ (fun _ => ∅) π

open scoped Classical in
noncomputable def membersP (γ : ℝ) [Fact (γ ≤ 1 / 2)] {p : ℕ} {kind : Bool} {A : Finset (LayeredGarden (2 * R))} {mk : Stage1Mk.MarkFn γ (2 * R)}
    (c : ClA γ R p kind A mk) : Finset (LayeredGarden (2 * R)) := A.filter (· ∈ c.1)

/-- The selection of a piece: the garden `LG` carries a prescribed point of the tau class whose `σ` holds at `κ`.
B1a: for the fine marking `mk`. -/
def selPMk (γ : ℝ) [Fact (γ ≤ 1 / 2)] (p : ℕ) (kind : Bool) (A : Finset (LayeredGarden (2 * R))) (P : WTParams) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (mk : Stage1Mk.MarkFn γ (2 * R)) (π : PcA γ R p kind A mk)
    (LG : LayeredGarden (2 * R)) (κ : GenDecoration LG.garden P.d roots 0) : Prop :=
  ∃ (b : VineA.PrescribedPrimeGarden γ (2 * R)) (h : b.layered = LG), VineA.PrescribedPrimeGarden.Related γ (p := p) (kind := kind) (repPt γ π) b mk ∧
    selAt γ P base b.prime b.sigma (h ▸ κ)

/-- The selection of a piece (main's: `selPMk` at the empty fine marking). -/
abbrev selP (γ : ℝ) [Fact (γ ≤ 1 / 2)] (p : ℕ) (kind : Bool) (A : Finset (LayeredGarden (2 * R))) (P : WTParams) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) : (π : PcA γ R p kind A) → (LG : LayeredGarden (2 * R)) →
      GenDecoration LG.garden P.d roots 0 → Prop :=
  selPMk γ p kind A P base roots fun _ => ∅

/-- B1b-2 (Mk-general form of `coarse_eq_of_related`): fine′ related points (fine marking `mkF`) have the same coarse′
class (coarse marking `mkC ⊆ mkF`, carried by every batch: the world's `markInvariantBatchV_markI0`). No transport of
the fine marking is needed: each fine′ batch edge already lands in the source's coarse′ class. -/
theorem coarse_eq_of_relatedMk {p : ℕ} {kind : Bool} {mkF mkC : Stage1Mk.MarkFn γ (2 * R)}
    (hV : Stage1Mk.MarkInvariantBatchV γ mkC fun _ => True)
    (hsub : ∀ {LG : LayeredGarden (2 * R)} (A : VineA.PrimeData LG), mkC A ⊆ mkF A)
    {a b : VineA.PrescribedPrimeGarden γ (2 * R)} (h : VineA.PrescribedPrimeGarden.Related γ (p := p) (kind := kind) a b mkF) :
    coarseOf γ p kind a mkC = coarseOf γ p kind b mkC := by
  induction h with
  | rel a b h => exact VineA.PrimeData.coarse_outputs_rebaseMk hV a.prime b.prime (VineA.PrescribedPrimeGarden.BatchReach.mem_coarseMk hsub h)
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih hj => exact ih.trans hj


end WaveTurbulence.GammaLow.Fama.Represents
