/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VinePrimeState` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.SourceStructure
public import WaveTurbulence.Foundations.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Group
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVC
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Rev
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Runs
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Top
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
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
/-! VINE-A1: canonical prime-skeleton representatives of ordinary canonical
objects γ of either kind, and their full / sigma-selected LF family states.
REG-STRUCT provides source skeleton and replacement uniqueness. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.Twist WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.LFTwist WaveTurbulence.Reg.Skeleton WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]






/-- An actual family state γ over the selected core subcollection. -/
noncomputable def PrimeData.state {LG : LayeredGarden w} (γ : ℝ) [Fact (γ ≤ 1 / 2)] (A : PrimeData LG)
    (U : Set (CLVineG γ A.skeleton)) (hU : U ⊆ vinesVG γ A.skeleton) :
    FamilyReconstruction w (CoreIndex γ U) where
  skeleton := A.skeleton
  family := coreFamilyOf γ U hU
  plain := A.prime.1
  data := A.data
  layered := LG
  decodes := A.decodes


/-- The fine congruence state γ for a prescription uses precisely the core members of V0(sigma).  B1a: with the
trailing marked vine set `Mk` (default `∅`), the core members of the unmarked `𝒱₀♮ = vinesV0 γ A.skeleton σ Mk`
(twists only at unmarked vines). -/
noncomputable def PrimeData.fineState {LG : LayeredGarden w} (γ : ℝ) [Fact (γ ≤ 1 / 2)] (A : PrimeData LG)
    (σ : Prescription A.skeleton) (Mk : Set (CLVineG γ A.skeleton) := ∅) :
    FamilyReconstruction w (CoreIndex γ (vinesV0 γ A.skeleton σ Mk)) :=
  PrimeData.state γ A (vinesV0 γ A.skeleton σ Mk) (vinesV0_subsetMk A.skeleton σ Mk)


/-- Coarse′ family state γ of the probe (copied by source from the B0 probe, lines 216–219). -/
noncomputable def coarseStateMk {LG : LayeredGarden w} (γ : ℝ) [Fact (γ ≤ 1 / 2)] (A : PrimeData LG)
    (Mk : Set (CLVineG γ A.skeleton)) :
    LFTwist.FamilyReconstruction w (CoreIndex γ {c | c ∈ vinesVG γ A.skeleton ∧ c ∉ Mk}) :=
  PrimeData.state γ A {c | c ∈ vinesVG γ A.skeleton ∧ c ∉ Mk} (fun _ h => h.1)


/-- B1a bridge: the outputs of states over equal carriers agree. -/
theorem PrimeData.state_allCoreOutputs_congr {LG : LayeredGarden w} (A : PrimeData LG) {p : ℕ} {kind : Bool}
    {U V : Set (CLVineG γ A.skeleton)} (hUV : U = V) (hU : U ⊆ vinesVG γ A.skeleton) (hV : V ⊆ vinesVG γ A.skeleton) :
    (PrimeData.state γ A U hU).allCoreOutputs (p := p) (kind := kind) = (PrimeData.state γ A V hV).allCoreOutputs (p := p) (kind := kind) := by
  subst hUV; rfl







end WaveTurbulence.GammaLow.Fama.VineA
