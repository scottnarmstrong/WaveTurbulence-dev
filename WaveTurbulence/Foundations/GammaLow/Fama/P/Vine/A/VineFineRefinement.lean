/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineFineRefinement` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.Vine.A.VineRestrictionOutputs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineRebase
public import WaveTurbulence.Foundations.Vine.A.VinePrimeUnique
public import WaveTurbulence.Foundations.Vine.A.VineFineRefinement
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamilyUnique
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineBatch
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineOperation
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineRecovery
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineReindex
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport
/-! Actual fine garden output classes lie in their coarse class and rebase at every member. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open Stage1 Twist RedSplice LFTwist Reg.Skeleton WaveTurbulence.GammaLow.FinalCount
variable {w p : ℕ} {kind : Bool} {LG LH : LayeredGarden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- Include the exact canonical core coordinates of a smaller vine carrier. -/
def coreIndexInclusion (γ : ℝ) [Fact (γ ≤ 1 / 2)] {G : Garden w} {U V : Set (CLVineG γ G)} (h : U ⊆ V) : CoreIndex γ U → CoreIndex γ V :=
  fun i => ⟨i.1, h i.2.1, i.2.2⟩

theorem coreIndexInclusion_injective {G : Garden w} {U V : Set (CLVineG γ G)} (h : U ⊆ V) :
    Function.Injective (coreIndexInclusion γ h) := fun _ _ he => Subtype.ext (congrArg (fun j : CoreIndex γ V => j.1) he)

/-- Canonical geometric placements agree across a restriction of the exact vine carrier. -/
theorem coreFamilyOf_restrict {G : Garden w} (U V : Set (CLVineG γ G)) (hU : U ⊆ vinesVG γ G)
    (hV : V ⊆ vinesVG γ G) (hUV : U ⊆ V) :
    coreFamilyOf γ U hU = familyRestrict (coreFamilyOf γ V hV)
      (coreIndexInclusion γ hUV) (coreIndexInclusion_injective hUV) := by
  apply CoreFamily.ext_data
  · exact funext fun i => core_kind_unique (coreKind_spec U i) (coreKind_spec V (coreIndexInclusion γ hUV i))
  · rfl
  · rfl
  · exact funext fun i => placement_unique (corePlacementOf_spec U i)
      (corePlacementOf_spec V (coreIndexInclusion γ hUV i))

/-- The entire actual smaller state γ is the restriction of the larger canonical state. -/
theorem PrimeData.state_eq_restrict (A : PrimeData LG) (U V : Set (CLVineG γ A.skeleton))
    (hU : U ⊆ vinesVG γ A.skeleton) (hV : V ⊆ vinesVG γ A.skeleton) (hUV : U ⊆ V) :
    PrimeData.state γ A U hU = stateRestrict (PrimeData.state γ A V hV) (coreIndexInclusion γ hUV) (coreIndexInclusion_injective hUV) := by
  apply familyReconstruction_ext
  · rfl
  · exact heq_of_eq (coreFamilyOf_restrict U V hU hV hUV)
  · rfl
  · rfl


/-- B1b (R11): the fine′ class (marked set `Mk`) lies in the coarse′ class of any smaller marked set `Mk0`
(o75: the coarse marking `markI0` is contained in the fine marking `markI`). -/
theorem PrimeData.fine_outputs_subset_coarseMk (A : PrimeData LG) (σ : Prescription A.skeleton)
    {Mk Mk0 : Set (CLVineG γ A.skeleton)} (h : Mk0 ⊆ Mk) :
    (PrimeData.fineState γ A σ Mk).allCoreOutputs (p := p) (kind := kind) ⊆
      (coarseStateMk γ A Mk0).allCoreOutputs (p := p) (kind := kind) := by
  change (PrimeData.state γ A (vinesV0 γ A.skeleton σ Mk) (vinesV0_subsetMk A.skeleton σ Mk)).allCoreOutputs ⊆
    (PrimeData.state γ A {c | c ∈ vinesVG γ A.skeleton ∧ c ∉ Mk0} (fun _ h => h.1)).allCoreOutputs
  rw [PrimeData.state_eq_restrict A (vinesV0 γ A.skeleton σ Mk) {c | c ∈ vinesVG γ A.skeleton ∧ c ∉ Mk0} _ (fun _ h => h.1)
    (fun c hc => ⟨(mem_vinesV0.mp hc).1.1, fun hm => (mem_vinesV0.mp hc).2 (h hm)⟩)]
  exact allCoreOutputs_restrict_subset _ _ _




end WaveTurbulence.GammaLow.Fama.VineA
