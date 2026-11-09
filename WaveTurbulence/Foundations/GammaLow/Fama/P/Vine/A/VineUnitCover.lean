/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineUnitCover` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.Vine.A.VineUnitCover
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK2
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
/-! VINE-A1: the sigma-selected family is precisely the core part of V carried
by the actual S2a splice units, not a separately assumed subcollection. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.Twist WaveTurbulence.GammaLow.FinalCount

variable {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]


/-- B1b: the units of an SG group cover its unmarked `𝒱`-ingredients (main's `cover` for an unmarked group, the runs'
`cover` for a marked one). -/
theorem groupUnitsMk_cover {w : ℕ} {G : Garden w} {Mk : Set (CLVineG γ G)}
    {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroupsG γ G.molecule) {c : CLVineG γ G} (hc : c ∈ vinesVG γ G) (hcM : c ∉ Mk)
    (hi : IsIngredientG γ G.molecule S c.atoms) : ∃ u ∈ groupUnitsMk γ G Mk S, c.atoms ⊆ u.atoms := by
  classical
  by_cases hm : markedGroup γ G Mk S
  · have hne := exists_markedGroupUnits hm
    have he : groupUnitsMk γ G Mk S = (Classical.choice hne).runs := by
      unfold groupUnitsMk
      simp only [hm, ↓reduceIte, dif_pos hne]
    rw [he]
    exact (Classical.choice hne).cover c hc hcM hi
  · rw [groupUnitsMk_of_not_marked hm]
    exact (groupUnitsOf γ G S).cover (Mole.garden_isMolecule G) hS c hc hi

/-- B1b (Mk-general form of `vinesV0_iff_unit_cover`): unmarked `𝒱₀` membership and the cover by the units (runs at
marked groups, which exist by B2a's `exists_markedGroupUnits`) coincide on the unmarked `𝒱` carrier. -/
theorem vinesV0_iff_unit_coverMk {w : ℕ} (G : Garden w) (σ : Prescription G) {Mk : Set (CLVineG γ G)}
    (c : CLVineG γ G) :
    c ∈ vinesV0 γ G σ Mk ↔ c ∈ vinesVG γ G ∧ c ∉ Mk ∧ ∃ u ∈ unitBlocks γ G σ Mk, c.atoms ⊆ u.atoms := by
  constructor
  · rintro ⟨hc, S, hS, hi, hσ, hcM⟩
    obtain ⟨u, hu, hcu⟩ := groupUnitsMk_cover hS hc hcM hi
    exact ⟨hc, hcM, u, mem_unitBlocksMk.mpr ⟨S, hS, hσ, hu⟩, hcu⟩
  · rintro ⟨hc, hcM, u, hu, hcu⟩
    have hc' := hc
    obtain ⟨S, hS, hi, hcond⟩ := hc
    obtain ⟨T, hT, hσ, hut⟩ := mem_unitBlocksMk.mp hu
    have he : S = T := by
      by_contra hne
      have hz := c.upper_mem
      exact (Finset.disjoint_left.mp (maximalGroups_disjoint (Mole.garden_isMolecule G) hS hT hne)
        (ing_subset hi hz) (groupUnitsMk_sub hut (hcu hz))).elim
    exact ⟨hc', S, hS, hi, he.symm ▸ hσ, hcM⟩



end WaveTurbulence.GammaLow.Fama.VineA
