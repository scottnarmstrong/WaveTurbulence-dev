/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineFamilyUnique` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineReindex
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.Vine.A.VineFamilyUnique
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
/-! VINE-A1: complete core-family data are unique up to their duplicate-free
index equivalence, including vine kinds and actual twist placements. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.GammaLow.FinalCount
variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]


/-- The reindexing preserves the exact source vine type as well as its geometry. -/
theorem indexEquiv_kind {ι : Type*} (F : CoreFamily G ι) (U : Set (CLVineG γ G))
    (hmem : ∀ i, familyVine γ F i ∈ U)
    (hcover : ∀ c ∈ U, (∃ X, IsCoreCLVine G X c.atoms c.upper c.lower) →
      ∃ i, F.atoms i = c.atoms) (i : ι) :
    coreKind γ U (indexEquiv γ F U hmem hcover i) = F.kind i :=
  core_kind_unique (coreKind_spec U _) (F.core i)

/-- All four actual data fields of CoreFamily agree under the unique vine reindexing. -/
theorem coreFamilyOf_reindex_data {ι : Type*} (F : CoreFamily G ι) (U : Set (CLVineG γ G))
    (hU : U ⊆ vinesVG γ G) (hmem : ∀ i, familyVine γ F i ∈ U)
    (hcover : ∀ c ∈ U, (∃ X, IsCoreCLVine G X c.atoms c.upper c.lower) →
      ∃ i, F.atoms i = c.atoms) :
    ∃ e : ι ≃ CoreIndex γ U, ∀ i,
      (coreFamilyOf γ U hU).kind (e i) = F.kind i ∧
      (coreFamilyOf γ U hU).atoms (e i) = F.atoms i ∧
      (coreFamilyOf γ U hU).upper (e i) = F.upper i ∧
      (coreFamilyOf γ U hU).placement (e i) = F.placement i := by
  refine ⟨indexEquiv γ F U hmem hcover, fun i => ?_⟩
  exact ⟨indexEquiv_kind F U hmem hcover i, rfl, rfl, indexEquiv_placement F U hmem hcover i⟩


end WaveTurbulence.GammaLow.Fama.VineA
