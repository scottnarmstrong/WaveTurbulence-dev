/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineReindex` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Core
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.Molecule.TwistFamilyExtensionality
public import WaveTurbulence.Foundations.Vine.A.VineReindex
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
/-! VINE-A1: duplicate-free enumeration and uniqueness up to reindexing of the
specified core vine carrier. Every statement concerns actual CoreFamily data. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.GammaLow.FinalCount
variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- The geometric CL vine represented by a family member. -/
def familyVine {ι : Type*} (γ : ℝ) [Fact (γ ≤ 1 / 2)] (F : CoreFamily G ι) (i : ι) : CLVineG γ G where
  atoms := F.atoms i
  upper := F.upper i
  lower := (F.placement i).lower
  isVine := isSomeVine_of_core (F.core i)
  notParentUpper := (F.core i).2.1.1
  parentLower := (F.core i).2.1.2



/-- Map any exact enumeration to the canonical subtype of the intended carrier. -/
noncomputable def indexEquiv {ι : Type*} (γ : ℝ) [Fact (γ ≤ 1 / 2)] (F : CoreFamily G ι) (U : Set (CLVineG γ G))
    (hmem : ∀ i, familyVine γ F i ∈ U)
    (hcover : ∀ c ∈ U, (∃ X, IsCoreCLVine G X c.atoms c.upper c.lower) →
      ∃ i, F.atoms i = c.atoms) : ι ≃ CoreIndex γ U := by
  let f : ι → CoreIndex γ U := fun i => ⟨familyVine γ F i, hmem i, F.kind i, F.core i⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    apply family_atoms_injective F
    exact congrArg (fun x : CoreIndex γ U => x.1.atoms) hij
  · intro c
    obtain ⟨i, hi⟩ := hcover c.1 c.2.1 c.2.2
    exact ⟨i, Subtype.ext (clVine_eq_of_atoms hi)⟩


/-- Consequently the chosen actual placements agree under the reindexing. -/
theorem indexEquiv_placement {ι : Type*} (F : CoreFamily G ι) (U : Set (CLVineG γ G))
    (hmem : ∀ i, familyVine γ F i ∈ U)
    (hcover : ∀ c ∈ U, (∃ X, IsCoreCLVine G X c.atoms c.upper c.lower) →
      ∃ i, F.atoms i = c.atoms) (i : ι) :
    corePlacementOf γ U (indexEquiv γ F U hmem hcover i) = F.placement i := by
  apply placement_unique (corePlacementOf_spec U _)
  exact F.designated i

end WaveTurbulence.GammaLow.Fama.VineA
