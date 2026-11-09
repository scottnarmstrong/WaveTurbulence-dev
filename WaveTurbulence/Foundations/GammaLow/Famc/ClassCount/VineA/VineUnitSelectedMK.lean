/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (item I, with L5a tool) of main `WaveTurbulence.Foundations.Vine.A.VineUnitSelectedMK` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelected
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK3
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Vine.A.VineUnitSelectedMK
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
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineChainNoCN
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunChain
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunSelected
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineSkipSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitCover
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitCoverOne
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineWholeUnit


/-!
# B2a MK-RUNS: `unitBlocks_selected_spine` for every marked vine set

B0 §5: the statements of the vine-side bridges hold for runs.  `unitBlocks_selected_spineMk` is main's
`unitBlocks_selected_spine` with the marked set `Mk` (at `Mk = ∅` it is main's statement): every unit of
`Fama.unitBlocks γ G σ Mk` (main's units of an unmarked group, the runs of a marked one) has a spine whose members are vines
of `𝒱₀♮ = Fama.vinesV0 γ G σ Mk`.  (`unitBlocks_chainMk` is B1a's, from the field `Fama.chain` supplied by
`Fama.exists_markedGroupUnits`.)
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Famc.ClassCount WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.GammaLow.FinalCount
variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant] [Fact TVineStructInputs]

/-- Every unit of a group (marked or not) has a spine of unmarked `𝒱`-ingredients of the group. -/
theorem groupUnitsMk_selected_spine {Mk : Set (CLVineG γ G)} {S : Finset (GBranch G.tree)}
    (hS : S ∈ maximalGroupsG γ G.molecule) {u : CLBlock G} (hu : u ∈ Fama.groupUnitsMk γ G Mk S) :
    ∃ L, Fama.Spine γ G.molecule L u.atoms u.upper u.lower ∧ ∀ t ∈ L, ∃ c : CLVineG γ G,
      c ∈ vinesVG γ G ∧ c ∉ Mk ∧ IsIngredientG γ G.molecule S c.atoms ∧ c.atoms = t.1 := by
  by_cases h : Fama.markedGroup γ G Mk S
  · -- marked group: the units are the runs of L5a's `MarkedGroupUnits`, whose `spine` field is the claim (main:
    -- `RedSplice.groupUnitsMk_spine_of_markedMK`, FinalCount/RedSpliceSurvMK2.lean)
    have hne := Fama.exists_markedGroupUnits h
    have he : Fama.groupUnitsMk γ G Mk S = (Classical.choice hne).runs := by
      unfold Fama.groupUnitsMk
      simp only [h, ↓reduceIte, dif_pos hne]
    rw [he] at hu
    exact (Classical.choice hne).spine u hu
  · rw [Fama.groupUnitsMk_of_not_marked h] at hu
    obtain ⟨L, hs, hsel⟩ := groupUnit_selected_spine (Fama.groupUnitsOf γ G S) hS hu
    refine ⟨L, hs, fun t ht => ?_⟩
    obtain ⟨c, hc, he⟩ := hsel t ht
    have hci : IsIngredientG γ G.molecule S c.atoms := by
      obtain ⟨S', hS', hi', _⟩ := hc
      have hin : c.atoms ⊆ S := he ▸ (hs.mem_vine ht).2.trans ((Fama.groupUnitsOf γ G S).sub u hu)
      have heS : S' = S := by
        by_contra hne
        exact (disjoint_left.mp (Fama.groups_disjoint' (Mole.garden_isMolecule G) hS' hS hne)
          (Fama.ingredient_sub hi' c.upper_mem)) (hin c.upper_mem)
      exact heS ▸ hi'
    exact ⟨c, hc, Fama.not_mem_of_not_markedGroup h hc hci, hci, he⟩

/-- **`unitBlocks_selected_spine` for every marked vine set**: every unit is a spine of `𝒱₀♮` vines. -/
theorem unitBlocks_selected_spineMk {σ : Prescription G} {Mk : Set (CLVineG γ G)} {u : CLBlock G}
    (hu : u ∈ Fama.unitBlocks γ G σ Mk) :
    ∃ L, Fama.Spine γ G.molecule L u.atoms u.upper u.lower ∧ ∀ t ∈ L, ∃ c ∈ Fama.vinesV0 γ G σ Mk, c.atoms = t.1 := by
  obtain ⟨S, hS, hσ, hum⟩ := Fama.mem_unitBlocksMk.mp hu
  obtain ⟨L, hs, hsel⟩ := groupUnitsMk_selected_spine hS hum
  refine ⟨L, hs, fun t ht => ?_⟩
  obtain ⟨c, hc, hcMk, hci, he⟩ := hsel t ht
  exact ⟨c, ⟨hc, S, hS, hci, hσ, hcMk⟩, he⟩

end WaveTurbulence.GammaLow.Famc.VineA
